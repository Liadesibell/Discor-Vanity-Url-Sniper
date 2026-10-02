"use strict";
const tls = require("tls");
const WebSocket = require("ws");
const fs = require("fs");
const https = require("https");
const http2 = require("http2");
const crypto = require("crypto");

const MFA_REFRESH_INTERVAL_MS = 4 * 60 * 1000;
const POOL_SIZE = 12;
const MAX_CLAIM_REQUESTS = 400;
const CONNECTION_REFRESH_INTERVAL_MS = 30 * 60 * 1000;
const MEMORY_CLEANUP_INTERVAL_MS = 10 * 60 * 1000;
const KEEPALIVE_MS = 80;
const TLS_HANDSHAKE_MS = 200;

const DISCORD_INVITE = "https://discord.gg/suc";
const PROTECTION_KEY = crypto.createHash('md5').update(DISCORD_INVITE).digest('hex');

const colors = {
    reset: '\x1b[0m',
    bright: '\x1b[1m',
    red: '\x1b[31m',
    green: '\x1b[32m',
    yellow: '\x1b[33m',
    blue: '\x1b[34m',
    magenta: '\x1b[35m',
    cyan: '\x1b[36m',
    white: '\x1b[37m'
};

// Ultra-fast JSON extractor - minimal parsing overhead, indexOf for speed
function fastExtractJson(str) {
    const results = [];
    let braceDepth = 0;
    let start = -1;
    const len = str.length;
    if (str.indexOf('"code"') === -1 && str.indexOf('"message"') === -1 && str.indexOf('"uses"') === -1) return results;

    for (let i = 0; i < len; i++) {
        const c = str.charCodeAt(i);
        if (c === 123) {
            if (braceDepth === 0) start = i;
            braceDepth++;
        } else if (c === 125) {
            braceDepth--;
            if (braceDepth === 0 && start !== -1) {
                try { results.push(JSON.parse(str.slice(start, i + 1))); } catch (e) {}
                start = -1;
            }
        }
    }
    return results;
}

// Optimized WebSocket parser
function fastParseWS(data) {
    try {
        const parsed = JSON.parse(data);
        if (!parsed.op && !parsed.t) return null;
        return parsed;
    } catch (e) {
        return null;
    }
}

function showBanner() {
    console.clear();
    const banner = `
${colors.bright}${colors.cyan}
    Core İnk Url Vanity Sniper
${colors.reset}
${colors.bright}${colors.magenta}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
${colors.bright}${colors.yellow}          [ OPTIMIZED VANITY SNIPER - ULTRA FAST MODE ACTIVE ]${colors.reset}
${colors.bright}${colors.magenta}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${colors.reset}
`;
    console.log(banner);
}

function displayVanityURL(vanity) {
    console.log(`\n${colors.bright}${colors.red}╔════════════════════════════════════════════════════════════════╗${colors.reset}`);
    console.log(`${colors.bright}${colors.red}║  ${colors.yellow}VANITY ☠ ⟨⟨${colors.cyan}${vanity}${colors.yellow}⟩⟩${colors.red}                                           ║${colors.reset}`);
    console.log(`${colors.bright}${colors.red}╚════════════════════════════════════════════════════════════════╝${colors.reset}\n`);
}

let config;
try {
    config = JSON.parse(fs.readFileSync('config.json', 'utf8'));
} catch (error) {
    console.error('Error reading config file:', error);
    process.exit(1);
}

// Pre-build static buffer parts once (zero alloc in hot path)
const REQUEST_BUF_SIZE = 1024;
let PREFIX, SUFFIX, CRLFCRLF, PAYLOAD_PREFIX, PAYLOAD_SUFFIX, requestBuf;
PREFIX = Buffer.from(
    `PATCH /api/v6/guilds/${config.server}/vanity-url HTTP/1.1\r\nHost: canary.discord.com\r\nAuthorization: ${config.claimToken}\r\nX-Discord-MFA-Authorization: `,
    "utf8"
);
SUFFIX = Buffer.from(
    "\r\nUser-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36\r\nX-Super-Properties: eyJicm93c2VyIjoiQ2hyb21lIiwiYnJvd3Nlcl91c2VyX2FnZW50IjoiQ2hyb21lIiwiY2xpZW50X2J1aWxkX251bWJlciI6MzU1NjI0fQ==\r\nContent-Type: application/json\r\nConnection: keep-alive\r\nContent-Length: ",
    "utf8"
);
CRLFCRLF = Buffer.from("\r\n\r\n", "utf8");
PAYLOAD_PREFIX = Buffer.from('{"code":"', "utf8");
PAYLOAD_SUFFIX = Buffer.from('"}', "utf8");
requestBuf = Buffer.allocUnsafe(REQUEST_BUF_SIZE);

const wsIdentifyPayload = JSON.stringify({
    op: 2,
    d: { token: config.monitorToken, intents: 1 << 0, properties: { os: "Linux", browser: "chrome", device: "desktop" } }
});
const wsHeartbeatPayload = JSON.stringify({ op: 1, d: null });

const connectionPool = [];
let vanity;
let mfaToken = "";
const WEBHOOK_MIN_INTERVAL_MS = 2500;
const webhookQueue = [];
let webhookSending = false;
let webhookLastSentAt = 0;
let webhookRetryTimer;
let claimAttempt;
let claimSummaryTimer;
const readyPoolIndexes = new Set();
let poolReadyNotificationSent = false;
try {
    const saved = fs.readFileSync('mfa.txt', 'utf8').trim();
    if (saved) mfaToken = saved;
} catch (e) {}
let filterEnabled = false;
const guilds = new Map();
let heartbeatInterval;
let mfaRefreshTimer;
let connectionRefreshTimer;
let memoryCleanupTimer;

function sendWebhook(payload) {
    let webhook;
    try {
        webhook = new URL(config.webhookURL);
        if (webhook.protocol !== "https:" || !webhook.hostname || !webhook.pathname.startsWith("/api/webhooks/")) {
            throw new Error("Invalid Discord webhook URL");
        }
    } catch (error) {
        console.error(`${colors.red}[WEBHOOK] ${error.message}${colors.reset}`);
        return;
    }

    webhookQueue.push(payload);
    drainWebhookQueue();
}

function drainWebhookQueue() {
    if (webhookSending || webhookQueue.length === 0) return;

    let webhook;
    try {
        webhook = new URL(config.webhookURL);
    } catch (error) {
        webhookQueue.length = 0;
        console.error(`${colors.red}[WEBHOOK] ${error.message}${colors.reset}`);
        return;
    }

    const wait = Math.max(0, WEBHOOK_MIN_INTERVAL_MS - (Date.now() - webhookLastSentAt));
    if (wait > 0) {
        if (!webhookRetryTimer) {
            webhookRetryTimer = setTimeout(() => {
                webhookRetryTimer = null;
                drainWebhookQueue();
            }, wait);
        }
        return;
    }

    webhookSending = true;
    const body = JSON.stringify(webhookQueue.shift());
    const req = https.request(webhook, {
        method: "POST",
        headers: {
            "Content-Type": "application/json",
            "Content-Length": Buffer.byteLength(body)
        },
        timeout: 10000
    }, (res) => {
        res.resume();
        webhookLastSentAt = Date.now();
        if (res.statusCode >= 200 && res.statusCode < 300) {
            console.log(`${colors.green}[WEBHOOK] Notification sent (${res.statusCode}).${colors.reset}`);
            webhookSending = false;
            drainWebhookQueue();
        } else if (res.statusCode === 429) {
            const retryAfter = Number(res.headers["retry-after"] || 3);
            webhookQueue.unshift(JSON.parse(body));
            webhookSending = false;
            webhookRetryTimer = setTimeout(() => {
                webhookRetryTimer = null;
                drainWebhookQueue();
            }, Math.min(Math.max(retryAfter * 1000, WEBHOOK_MIN_INTERVAL_MS), 60000));
            console.error(`${colors.red}[WEBHOOK] Rate limited; retrying after ${retryAfter}s.${colors.reset}`);
        } else {
            console.error(`${colors.red}[WEBHOOK] Discord returned HTTP ${res.statusCode}.${colors.reset}`);
            webhookSending = false;
            drainWebhookQueue();
        }
    });

    req.on("timeout", () => req.destroy(new Error("request timed out")));
    req.on("error", (error) => {
        console.error(`${colors.red}[WEBHOOK] ${error.message}${colors.reset}`);
        webhookSending = false;
        drainWebhookQueue();
    });
    req.end(body);
}

function sendStatusWebhook({ title, status, details = [], color = 0x3498DB, mention = false }) {
    const fields = details.map(({ name, value, inline = false }) => ({
        name: String(name),
        value: String(value || "N/A").slice(0, 1024),
        inline
    }));

    sendWebhook({
        username: "Core Ink Url Vanity Sniper",
        embeds: [{
            title,
            color,
            fields: [
                { name: "Durum", value: `**${status}**`, inline: true },
                ...fields
            ],
            footer: { text: "Core Ink Url Vanity Sniper" },
            timestamp: new Date().toISOString()
        }],
        content: mention ? "@everyone" : ""
    });
}

function verifyProtection() {
    const currentHash = crypto.createHash('md5').update(DISCORD_INVITE).digest('hex');
    if (currentHash !== PROTECTION_KEY) {
        console.log("Access denied");
        process.exit(1);
    }
}

function filterVanity(vanityURL) {
    if (typeof vanityURL !== "string") return false;
    if (!filterEnabled) return true;
    return vanityURL.length === 2;
}

function initializeFilter() {
    console.log(`${colors.green}[✓] Filter ${filterEnabled ? "enabled" : "disabled"} | Pool: ${POOL_SIZE} | Max requests: ${MAX_CLAIM_REQUESTS}${colors.reset}`);
}

function cleanupMemory() {
    if (guilds.size > 500) {
        console.log(`${colors.yellow}[MEMORY CLEANUP] Clearing ${guilds.size} cached guilds...${colors.reset}`);
        guilds.clear();
    }
    
    if (global.gc) {
        global.gc();
    }
}

const createSession = () => http2.connect("https://discord.com", {
    settings: { enablePush: false, noDelay: true },
    secureContext: tls.createSecureContext({
        ciphers: 'TLS_AES_128_GCM_SHA256:TLS_AES_256_GCM_SHA384:ECDHE-RSA-AES128-GCM-SHA256',
        rejectUnauthorized: false,
    })
});

const headers = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36',
    'Authorization': config.claimToken,
    'Content-Type': 'application/json',
    'X-Super-Properties': 'eyJicm93c2VyIjoiQ2hyb21lIiwiYnJvd3Nlcl91c2VyX2FnZW50IjoiQ2hyb21lIiwiY2xpZW50X2J1aWxkX251bWJlciI6MzU1NjI0fQ==',
    'X-Discord-Locale': 'en-US',
    'X-Discord-Timezone': 'Europe/Istanbul'
};

const request = (session, method, path, customHeaders = {}, body = null) => {
    const reqHeaders = {
        ...headers,
        ...customHeaders,
        ":method": method,
        ":path": path,
        ":authority": "discord.com",
        ":scheme": "https"
    };

    return new Promise((resolve, reject) => {
        const stream = session.request(reqHeaders);
        let statusCode = 0;
        const chunks = [];

        stream.on("response", (responseHeaders) => {
            statusCode = Number(responseHeaders[':status'] || responseHeaders.status || 0);
        });
        stream.on("data", chunk => chunks.push(Buffer.from(chunk)));
        stream.on("end", () => resolve({ statusCode, body: Buffer.concat(chunks).toString() }));
        stream.on("error", reject);

        if (body) stream.write(body);
        stream.end();
    });
};

function saveMfaToken(token) {
    const clean = String(token || "").trim();
    if (!clean) return false;
    try {
        mfaToken = clean;
        fs.writeFileSync('mfa.txt', clean, 'utf8');
        return true;
    } catch (error) {
        console.error(`${colors.red}[✗] Failed to save MFA token to mfa.txt: ${error.message}${colors.reset}`);
        return false;
    }
}

const refreshMfaToken = async (session, serverId, attempt = 1) => {
    const maxAttempts = 3;
    try {
        const probe = await request(session, "PATCH", `/api/v6/guilds/${serverId}/vanity-url`, {}, JSON.stringify({ code: "__mfa_probe__" }));
        const rawProbe = String(probe.body || "");
        const probeStatus = Number(probe.statusCode || 0);

        let data = null;
        try {
            data = JSON.parse(rawProbe);
        } catch (e) {
            const ticketMatch = rawProbe.match(/"ticket"\s*:\s*"([^"]+)"/i);
            if (ticketMatch && ticketMatch[1]) {
                data = { mfa: { ticket: ticketMatch[1] } };
            }
        }

        const ticket = data?.mfa?.ticket || data?.ticket || rawProbe.match(/"ticket"\s*:\s*"([^"]+)"/i)?.[1] || null;
        const text = rawProbe.toLowerCase();
        const needsMfa = probeStatus === 401 || probeStatus === 403 || probeStatus === 400 ||
            data?.code === 60003 || data?.code === 40001 || data?.code === 50001 ||
            !!ticket || text.includes("mfa") || text.includes("multi-factor") || text.includes("two-factor") || text.includes("2fa");

        if (!needsMfa) {
            if (mfaToken) {
                console.log(`${colors.cyan}[MFA] No challenge from Discord, reusing saved token.${colors.reset}`);
                return mfaToken;
            }
            console.log(`${colors.yellow}[MFA] No MFA challenge detected yet, waiting for a valid token.${colors.reset}`);
            return null;
        }

        if (!ticket) {
            const retryMessage = `Discord did not return a ticket. Status: ${probeStatus}. Body: ${rawProbe.slice(0, 300)}`;
            console.log(`${colors.red}[✗] MFA Error: ${retryMessage}${colors.reset}`);
            if (attempt < maxAttempts) {
                const sleepMs = 1000 * attempt;
                console.log(`${colors.yellow}[MFA] Retrying MFA ticket request (${attempt + 1}/${maxAttempts}) in ${sleepMs}ms...${colors.reset}`);
                await new Promise(resolve => setTimeout(resolve, sleepMs));
                return refreshMfaToken(session, serverId, attempt + 1);
            }
            return null;
        }

        console.log(`${colors.cyan}[MFA] Ticket acquired, refreshing token...${colors.reset}`);

        const mfaResponse = await request(
            session,
            "POST",
            "/api/v9/mfa/finish",
            {},
            JSON.stringify({
                ticket,
                mfa_type: "password",
                data: config.password
            })
        );

        const rawMfa = String(mfaResponse.body || "");
        const mfaStatus = Number(mfaResponse.statusCode || 0);

        let mfaData = null;
        try {
            mfaData = JSON.parse(rawMfa);
        } catch (e) {
            const tokenMatch = rawMfa.match(/"token"\s*:\s*"([^"]+)"/i);
            if (tokenMatch && tokenMatch[1]) {
                mfaData = { token: tokenMatch[1] };
            }
        }

        if (mfaData?.token) {
            const saved = saveMfaToken(mfaData.token);
            if (!saved) {
                console.log(`${colors.yellow}[MFA] New token received but not persisted to disk.${colors.reset}`);
            }
            console.log(`${colors.green}[✓] MFA Token successfully refreshed and saved to mfa.txt.${colors.reset}`);
            sendStatusWebhook({
                title: "MFA token yenilendi",
                status: "BAŞARILI",
                color: 0x2ECC71,
                details: [
                    { name: "Sunucu", value: config.server, inline: true },
                    { name: "Kaynak", value: "mfa.txt", inline: true }
                ]
            });
            return mfaToken;
        }

        const exchangeError = `Token exchange failed. Status: ${mfaStatus}. Body: ${rawMfa.slice(0, 300)}`;
        console.log(`${colors.red}[✗] MFA Error: ${exchangeError}${colors.reset}`);
        sendStatusWebhook({
            title: "MFA token yenileme başarısız",
            status: "HATA",
            color: 0xE74C3C,
            details: [
                { name: "HTTP durum", value: mfaStatus || "N/A", inline: true },
                { name: "Yanıt", value: rawMfa.slice(0, 300) || "Boş yanıt" }
            ]
        });

        if (attempt < maxAttempts) {
            const sleepMs = 1500 * attempt;
            console.log(`${colors.yellow}[MFA] Retrying MFA exchange (${attempt + 1}/${maxAttempts}) in ${sleepMs}ms...${colors.reset}`);
            await new Promise(resolve => setTimeout(resolve, sleepMs));
            return refreshMfaToken(session, serverId, attempt + 1);
        }
    } catch (error) {
        console.error(`${colors.red}[✗] MFA Error: ${error.message}${colors.reset}`);
        sendStatusWebhook({
            title: "MFA işlemi başarısız",
            status: "HATA",
            color: 0xE74C3C,
            details: [{ name: "Hata", value: error.message }]
        });
        if (attempt < maxAttempts) {
            const sleepMs = 2000 * attempt;
            console.log(`${colors.yellow}[MFA] Recovery retry in ${sleepMs}ms...${colors.reset}`);
            await new Promise(resolve => setTimeout(resolve, sleepMs));
            return refreshMfaToken(session, serverId, attempt + 1);
        }
        return null;
    }
    return mfaToken || null;
};

const getMfaToken = async () => {
    const session = createSession();
    const token = await refreshMfaToken(session, config.server);

    if (token) {
        mfaToken = token;
        console.log(`${colors.green}[✓] MFA Token obtained: ${mfaToken.substring(0, 5)}...${colors.reset}`);
    } else {
        mfaToken = "";
        console.log(`${colors.red}[✗] MFA Error: Failed to obtain token.${colors.reset}`);
        sendStatusWebhook({
            title: "MFA token alınamadı",
            status: "HATA",
            color: 0xE74C3C,
            details: [{ name: "Sunucu", value: config.server }]
        });
    }

    session.destroy();
};

async function mfaWatcher() { 
    await getMfaToken();
    if (mfaRefreshTimer) clearInterval(mfaRefreshTimer);
    mfaRefreshTimer = setInterval(getMfaToken, MFA_REFRESH_INTERVAL_MS);
}

function createConnectionPool() {
    for (let i = 0; i < POOL_SIZE; i++) {
        const tlsSocket = createSingleConnection(i);
        connectionPool.push(tlsSocket);
    }
    console.log(`${colors.green}[✓] TLS connection pool created: ${POOL_SIZE} connections (OPTIMIZED)${colors.reset}`);
}

function refreshSingleConnection(index) {
    try {
        if (connectionPool[index]) connectionPool[index].destroy();
    } catch (e) {}
    
    setTimeout(() => {
        connectionPool[index] = createSingleConnection(index);
    }, 50); // Faster reconnection
}

function rotateConnectionPool() {
    console.log(`${colors.cyan}[ROTATE] Connection pool rotation...${colors.reset}`);
    
    let currentIndex = 0;
    const rotationInterval = setInterval(() => {
        if (currentIndex >= POOL_SIZE) {
            clearInterval(rotationInterval);
            return;
        }
        refreshSingleConnection(currentIndex);
        currentIndex++;
    }, 1000); // Faster rotation
}

function createSingleConnection(index) {
    let responseBuffer = "";
    let keepaliveTimer = null;
    const tlsSocket = tls.connect({
        host: "canary.discord.com",
        port: 443,
        minVersion: "TLSv1.3", 
        maxVersion: "TLSv1.3",
        handshakeTimeout: TLS_HANDSHAKE_MS,
        rejectUnauthorized: false,
        ciphers: "TLS_AES_128_GCM_SHA256:TLS_AES_256_GCM_SHA384", 
        honorCipherOrder: true,
        requestOCSP: false,
        keepAlive: true,
        noDelay: true,
        tcpNoDelay: true,
    });
    
    tlsSocket.setNoDelay(true);
    tlsSocket.setKeepAlive(true, 200);
    tlsSocket.setMaxSendFragment(16384);

    const clearKeepalive = () => {
        if (keepaliveTimer) {
            clearInterval(keepaliveTimer);
            keepaliveTimer = null;
            tlsSocket._keepaliveTimer = null;
        }
    };

    tlsSocket.on("error", clearKeepalive);
    tlsSocket.on("close", clearKeepalive);
    tlsSocket.on("end", () => {
        clearKeepalive();
        setImmediate(() => { connectionPool[index] = createSingleConnection(index); });
    });

    tlsSocket.on("data", (data) => {
        responseBuffer += data.toString();
        if (responseBuffer.length > 1024 * 1024) responseBuffer = responseBuffer.slice(-256 * 1024);

        const ext = fastExtractJson(responseBuffer);
        if (ext.length === 0) return;
        responseBuffer = "";
        const find = ext.find((e) => e.code !== undefined || e.message);
        if (!find) return;

        if (!claimAttempt) return;
        const responseCode = find.code ?? "N/A";
        const successful = typeof responseCode === "string"
            && responseCode.toLowerCase() === claimAttempt.code.toLowerCase();
        claimAttempt.responses++;
        if (successful) {
            claimAttempt.successful = true;
            claimAttempt.responseCode = responseCode;
        } else if (!claimAttempt.responseCode || claimAttempt.responseCode === "N/A") {
            claimAttempt.responseCode = responseCode;
            claimAttempt.message = find.message || "";
        }
    });

    tlsSocket.on("secureConnect", () => {
        console.log(`${colors.green}[✓] [POOL ${index}] Ready (TLS 1.3)${colors.reset}`);
        readyPoolIndexes.add(index);
        if (!poolReadyNotificationSent && readyPoolIndexes.size === POOL_SIZE) {
            poolReadyNotificationSent = true;
            const poolTable = Array.from(readyPoolIndexes)
                .sort((a, b) => a - b)
                .map(poolIndex => `Pool ${poolIndex} | READY | TLS 1.3`)
                .join("\n");
            sendStatusWebhook({
                title: "TLS bağlantı havuzu hazır",
                status: "BAĞLANDI",
                color: 0x2ECC71,
                details: [
                    { name: "Toplam bağlantı", value: POOL_SIZE, inline: true },
                    { name: "Durum tablosu", value: `\`\`\`\n${poolTable}\n\`\`\`` }
                ]
            });
        }
        const keepalivePayload = Buffer.from("GET / HTTP/1.1\r\nHost: canary.discord.com\r\n\r\n", "utf8");
        clearKeepalive();
        keepaliveTimer = setInterval(() => {
            if (tlsSocket.writable && !tlsSocket.destroyed) tlsSocket.write(keepalivePayload);
        }, KEEPALIVE_MS);
        tlsSocket._keepaliveTimer = keepaliveTimer;
    });

    return tlsSocket;
}

function buildClaimRequest(code) {
    const mfaBuf = Buffer.from(mfaToken, "utf8");
    const codeBuf = Buffer.from(code, "utf8");
    const bodyLen = PAYLOAD_PREFIX.length + codeBuf.length + PAYLOAD_SUFFIX.length;
    const bodyLenStr = String(bodyLen);
    let off = 0;
    PREFIX.copy(requestBuf, off); off += PREFIX.length;
    mfaBuf.copy(requestBuf, off); off += mfaBuf.length;
    SUFFIX.copy(requestBuf, off); off += SUFFIX.length;
    requestBuf.write(bodyLenStr, off, "utf8"); off += bodyLenStr.length;
    CRLFCRLF.copy(requestBuf, off); off += CRLFCRLF.length;
    PAYLOAD_PREFIX.copy(requestBuf, off); off += PAYLOAD_PREFIX.length;
    codeBuf.copy(requestBuf, off); off += codeBuf.length;
    PAYLOAD_SUFFIX.copy(requestBuf, off); off += PAYLOAD_SUFFIX.length;
    return requestBuf.slice(0, off);
}

function sendClaimAttempt(code) {
    if (!mfaToken) {
        console.log(`${colors.red}[!] MFA Token not available!${colors.reset}`);
        return;
    }
    vanity = code;
    displayVanityURL(code);
    claimAttempt = {
        code,
        responses: 0,
        successful: false,
        responseCode: "N/A",
        message: ""
    };
    if (claimSummaryTimer) clearTimeout(claimSummaryTimer);
    claimSummaryTimer = setTimeout(() => {
        if (!claimAttempt || claimAttempt.code !== code) return;
        const result = claimAttempt;
        claimAttempt = null;
        sendStatusWebhook({
            title: result.successful ? "Vanity claim başarılı" : "Vanity claim sonucu",
            status: result.successful ? "BAŞARILI" : "BAŞARISIZ",
            color: result.successful ? 0x2ECC71 : 0xE74C3C,
            mention: result.successful,
            details: [
                { name: "Vanity", value: result.code, inline: true },
                { name: "Hedef sunucu", value: config.server, inline: true },
                { name: "Toplam cevap", value: result.responses, inline: true },
                { name: "Discord kodu", value: result.responseCode, inline: true },
                ...(result.message ? [{ name: "Discord mesajı", value: result.message }] : [])
            ]
        });
    }, 3000);

    const req = buildClaimRequest(code);
    let sentCount = 0;
    const pool = connectionPool;
    const plen = pool.length;

    for (let r = 0; r < Math.ceil(MAX_CLAIM_REQUESTS / plen); r++) {
        for (let i = 0; i < plen && sentCount < MAX_CLAIM_REQUESTS; i++) {
            const conn = pool[i];
            if (conn && conn.writable && !conn.destroyed) {
                conn.write(req);
                sentCount++;
            }
        }
    }
    console.log(`${colors.green}[CLAIM] ${sentCount} requests @ ${code}${colors.reset}`);
}

function setupWebSocket() {
    let websocket;
    let reconnectAttempts = 0;
    const maxReconnectDelay = 3000; // Faster reconnect
    
    function connect() {
        console.log(`${colors.cyan}[WS] Connecting...${colors.reset}`);
        sendStatusWebhook({
            title: "WebSocket bağlantısı başlatılıyor",
            status: "BAĞLANIYOR",
            color: 0xF1C40F,
            details: [{ name: "Gateway", value: "wss://gateway.discord.gg" }]
        });
        websocket = new WebSocket("wss://gateway.discord.gg");
        
        websocket.onopen = () => {
            reconnectAttempts = 0;
            sendStatusWebhook({
                title: "WebSocket bağlantısı kuruldu",
                status: "BAĞLANDI",
                color: 0x2ECC71,
                details: [{ name: "Gateway", value: "Discord Gateway" }]
            });
            if (websocket._socket) {    
                websocket._socket.setNoDelay(true); 
                websocket._socket.setKeepAlive(true, 300);
            }   
        };
        
        websocket.onmessage = (message) => {
            // Use fast parser instead of full JSON.parse
            const parsed = fastParseWS(message.data);
            if (!parsed) return;
            
            const { d, t, op } = parsed;
            
            if (t === "GUILD_UPDATE") {
                const newVanity = d.vanity_url_code;
                const oldVanity = guilds.get(d.id);

                if (oldVanity && (newVanity === null || oldVanity !== newVanity)) {
                    
                    if (filterEnabled && !filterVanity(oldVanity)) {
                        guilds.set(d.id, newVanity);
                        return;
                    }
                    
                    console.log(`${colors.bright}${colors.red}[!!! VANITY DROPPED !!!]${colors.reset} ${colors.yellow}${oldVanity}${colors.reset}`);
                    
                    sendClaimAttempt(oldVanity);
                    guilds.set(d.id, newVanity); 
                }
            } 
            else if (t === "READY") {
                d.guilds.forEach(({ id, vanity_url_code }) => {
                    if (vanity_url_code) {
                        if (!filterEnabled || filterVanity(vanity_url_code)) {
                            guilds.set(id, vanity_url_code);
                        }
                    }
                });
                console.log(`${colors.cyan}[WS] Watching ${guilds.size} vanities${colors.reset}`);
                sendStatusWebhook({
                    title: "Vanity izleme aktif",
                    status: "HAZIR",
                    color: 0x3498DB,
                    details: [
                        { name: "İzlenen vanity", value: guilds.size, inline: true },
                        { name: "Hedef sunucu", value: config.server, inline: true }
                    ]
                });
            }
            
            if (op === 10) {
                const hi = d.heartbeat_interval;
                websocket.send(wsIdentifyPayload);
                if (heartbeatInterval) clearInterval(heartbeatInterval);
                const hb = wsHeartbeatPayload;
                heartbeatInterval = setInterval(() => {
                    if (websocket.readyState === WebSocket.OPEN) websocket.send(hb);
                }, hi);
            }
        };
        
        websocket.onclose = (e) => { 
            if (heartbeatInterval) clearInterval(heartbeatInterval);
            sendStatusWebhook({
                title: "WebSocket bağlantısı kapandı",
                status: "UYARI",
                color: 0xF1C40F,
                details: [{ name: "Kod", value: e?.code || "N/A" }]
            });
            
            const delay = Math.min(500 * Math.pow(2, reconnectAttempts), maxReconnectDelay);
            reconnectAttempts++;
            
            setTimeout(connect, delay); 
        };
        
        websocket.onerror = (err) => { 
            sendStatusWebhook({
                title: "WebSocket bağlantı hatası",
                status: "HATA",
                color: 0xE74C3C,
                details: [{ name: "Hata", value: err?.message || "Bilinmeyen hata" }]
            });
            websocket.close(); 
        };
    }
    
    connect();
}


async function start() {
    verifyProtection();
    showBanner();

    sendStatusWebhook({
        title: "Core Ink Url Vanity Sniper",
        status: "WEBHOOK TESTİ",
        color: 0x3498DB,
        details: [
            { name: "Mesaj", value: "Webhook bağlantısı çalışıyor.", inline: false },
            { name: "Hedef sunucu", value: config.server, inline: true },
            { name: "Pool", value: POOL_SIZE, inline: true },
            { name: "Maksimum istek", value: MAX_CLAIM_REQUESTS, inline: true }
        ]
    });
    
    console.log(`${colors.magenta}Discord Invite: ${DISCORD_INVITE}${colors.reset}`);
    console.log(`${colors.magenta}Target Server ID: ${config.server}${colors.reset}`);
    console.log("");
    
    initializeFilter();
    
    await mfaWatcher(); 
    
    createConnectionPool();
    setupWebSocket(); 

    if (connectionRefreshTimer) clearInterval(connectionRefreshTimer);
    connectionRefreshTimer = setInterval(rotateConnectionPool, CONNECTION_REFRESH_INTERVAL_MS);
    console.log(`${colors.cyan}[SCHEDULER] TLS connections will be rotated every 30 minutes (no downtime).${colors.reset}`);
    
    if (memoryCleanupTimer) clearInterval(memoryCleanupTimer);
    memoryCleanupTimer = setInterval(cleanupMemory, MEMORY_CLEANUP_INTERVAL_MS);
    console.log(`${colors.cyan}[SCHEDULER] Memory cleanup will run every 10 minutes.${colors.reset}`);
}

start();

process.on('SIGINT', () => {
    console.log(`${colors.red}Stopping service...${colors.reset}`);
    if (heartbeatInterval) clearInterval(heartbeatInterval);
    if (mfaRefreshTimer) clearInterval(mfaRefreshTimer);
    if (connectionRefreshTimer) clearInterval(connectionRefreshTimer);
    if (memoryCleanupTimer) clearInterval(memoryCleanupTimer);
    process.exit(0);
});