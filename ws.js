const WebSocket = require('ws');

const ws = new WebSocket('wss://gateway.discord.gg/?v=9&encoding=json');

ws.on('open', () => {
  console.log('Bağlandı!');
});

ws.on('message', (data) => {
  console.log(data);
});

ws.on('error', (err) => {
  console.error(err);
});