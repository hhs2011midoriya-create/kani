import http from 'node:http';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const ALPHABET = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
export const MAX_MESSAGE_BYTES = 128 * 1024;
const MAX_BUFFERED_BYTES = 1024 * 1024;
const MODES = new Set(['reverse', 'shogi', 'chess', 'go', 'reversi']);
const TYPES = new Set(['create', 'join', 'ready', 'start', 'leave', 'sync', 'action', 'state', 'combat_input', 'combat_state', 'combat_end', 'ping']);
const utf8 = new TextDecoder('utf-8', { fatal: true });
const plain = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const integer = (value, low, high) => Number.isInteger(value) && value >= low && value <= high;

function frame(opcode, payload = Buffer.alloc(0)) {
  const bytes = Buffer.isBuffer(payload) ? payload : Buffer.from(payload);
  const header = Buffer.alloc(bytes.length < 126 ? 2 : bytes.length <= 65535 ? 4 : 10);
  header[0] = 0x80 | opcode;
  if (header.length === 2) header[1] = bytes.length;
  else if (header.length === 4) { header[1] = 126; header.writeUInt16BE(bytes.length, 2); }
  else { header[1] = 127; header.writeBigUInt64BE(BigInt(bytes.length), 2); }
  return Buffer.concat([header, bytes]);
}

function safeShape(value, depth = 0, budget = { remaining: 16000 }) {
  if (--budget.remaining < 0 || depth > 24) return false;
  if (value === null || typeof value === 'boolean') return true;
  if (typeof value === 'number') return Number.isFinite(value);
  if (typeof value === 'string') return value.length <= 16384;
  if (Array.isArray(value)) return value.length <= 4096 && value.every(v => safeShape(v, depth + 1, budget));
  if (!plain(value)) return false;
  return Object.entries(value).every(([key, child]) => !['__proto__', 'prototype', 'constructor'].includes(key)
    && key.length <= 80 && safeShape(child, depth + 1, budget));
}

function nickname(value) {
  if (typeof value !== 'string') return null;
  const name = value.trim();
  return [...name].length >= 1 && [...name].length <= 24 && !/[\u0000-\u001f\u007f]/u.test(name) ? name : null;
}

/** Dependency-free RFC6455 text transport and host-authoritative room relay.
 * The server verifies membership/turn/revision; it does not simulate game rules.
 * A malicious host can cheat. There is no account, reconnect, or migration layer.
 */
export function createRoomServer(options = {}) {
  const rooms = new Map();
  const peers = new Set();
  const staticRoot = path.resolve(options.staticRoot ?? path.join(HERE, '../dist'));
  const maxRooms = options.maxRooms ?? 128;
  const maxPeers = options.maxPeers ?? 512;
  const maxPeersPerIP = options.maxPeersPerIP ?? 16;
  const idleMs = options.idleMs ?? 60 * 60 * 1000;
  const allowedOrigins = options.allowedOrigins ?? [];
  let shuttingDown = false;

  function send(peer, data) {
    if (!peer || peer.closed || peer.socket.destroyed) return;
    const payload = Buffer.from(JSON.stringify(data));
    if (payload.length > MAX_MESSAGE_BYTES || peer.socket.writableLength > MAX_BUFFERED_BYTES) {
      peer.close(1009, 'Send buffer limit'); return;
    }
    peer.socket.write(frame(1, payload));
  }
  const fail = (peer, code, message = code) => send(peer, { type: 'error', code, message });
  function metadata(room) {
    return { code: room.code, capacity: room.capacity, teams: room.teams, mode: room.mode,
      started: room.started, paused: room.paused, host: 0,
      players: room.players.filter(Boolean).map(p => ({ slot: p.slot, name: p.name, connected: Boolean(p.peer), ready: p.ready })) };
  }
  function broadcast(room, data, except = null) {
    for (const player of room.players) if (player?.peer && player.peer !== except) send(player.peer, data);
  }
  const announceRoom = room => broadcast(room, { type: 'room', room: metadata(room) });
  function closeRoom(room, reason) {
    broadcast(room, { type: 'room_closed', reason });
    for (const player of room.players) if (player?.peer) { player.peer.room = null; player.peer.slot = null; }
    rooms.delete(room.code);
  }
  function depart(peer, reason = 'disconnected') {
    const room = peer.room;
    if (!room) return;
    const slot = peer.slot;
    peer.room = null; peer.slot = null;
    if (slot === 0) { closeRoom(room, 'host_left'); return; }
    if (!room.players[slot]) return;
    room.players[slot].peer = null;
    if (room.started) {
      room.paused = true;
      room.pendingAction = false;
      room.combat = null;
      broadcast(room, { type: 'peer_disconnected', slot, reason, paused: true, combat_aborted: true });
    } else {
      room.players[slot] = null;
      broadcast(room, { type: 'peer_disconnected', slot, reason, paused: false, combat_aborted: false });
    }
    room.touched = Date.now();
    announceRoom(room);
  }
  function joinRoom(peer, room, name, slot) {
    peer.room = room; peer.slot = slot;
    room.players[slot] = { slot, name, ready: false, peer };
    room.touched = Date.now();
    send(peer, { type: 'joined', slot, room: metadata(room) });
    announceRoom(room);
  }
  function handle(peer, message) {
    if (!plain(message) || !safeShape(message) || typeof message.type !== 'string' || !TYPES.has(message.type)) {
      fail(peer, 'invalid_message', 'Unsupported or malformed message'); return;
    }
    const now = Date.now();
    peer.tokens = Math.min(360, peer.tokens + (now - peer.tokenTime) * 0.18);
    peer.tokenTime = now;
    if (peer.tokens < 1) { peer.close(1008, 'Rate limit'); return; }
    peer.tokens -= 1;
    peer.lastActivity = now;
    const type = message.type;
    if (type === 'ping') { send(peer, { type: 'pong' }); return; }
    if (type === 'create' || type === 'join') {
      if (peer.room) { fail(peer, 'already_in_room'); return; }
      peer.lobbyTokens = Math.min(20, peer.lobbyTokens + (now - peer.lobbyTime) / 3000);
      peer.lobbyTime = now;
      if (peer.lobbyTokens < 1) { fail(peer, 'lobby_rate_limit'); return; }
      peer.lobbyTokens -= 1;
      const name = nickname(message.name);
      if (!name) { fail(peer, 'invalid_name', 'Name must contain 1–24 visible characters'); return; }
      if (type === 'create') {
        if (![2, 4].includes(message.capacity) || typeof message.teams !== 'boolean' || !MODES.has(message.mode)
            || (message.teams && message.capacity !== 4)) { fail(peer, 'invalid_room_options'); return; }
        if (rooms.size >= maxRooms) { fail(peer, 'server_full'); return; }
        let code;
        do { code = [...crypto.randomBytes(8)].map(byte => ALPHABET[byte & 31]).join(''); } while (rooms.has(code));
        const room = { code, capacity: message.capacity, teams: message.teams, mode: message.mode,
          started: false, paused: false, players: Array(message.capacity).fill(null), touched: now,
          revision: -1, snapshot: null, combat: null, pendingAction: false };
        rooms.set(code, room);
        joinRoom(peer, room, name, 0);
      } else {
        const code = typeof message.code === 'string' ? message.code.trim().toUpperCase() : '';
        if (!/^[A-HJ-NP-Z2-9]{8}$/u.test(code)) { fail(peer, 'invalid_code'); return; }
        const room = rooms.get(code);
        if (!room) { fail(peer, 'room_not_found'); return; }
        if (room.started || room.paused) { fail(peer, 'match_already_started', 'Rejoin is unavailable; create a fresh room for a new match'); return; }
        const slot = room.players.findIndex(player => player === null);
        if (slot < 0) { fail(peer, 'room_full'); return; }
        joinRoom(peer, room, name, slot);
      }
      return;
    }
    const room = peer.room;
    if (!room || rooms.get(room.code) !== room || room.players[peer.slot]?.peer !== peer) { fail(peer, 'not_in_room'); return; }
    room.touched = now;
    if (type === 'leave') { depart(peer, 'left'); send(peer, { type: 'left' }); return; }
    if (type === 'sync') {
      send(peer, { type: 'room', room: metadata(room) });
      if (room.snapshot) send(peer, room.snapshot);
      return;
    }
    if (type === 'ready') {
      if (room.started || typeof message.ready !== 'boolean') { fail(peer, 'invalid_ready'); return; }
      room.players[peer.slot].ready = message.ready;
      announceRoom(room); return;
    }
    if (type === 'start') {
      if (peer.slot !== 0) { fail(peer, 'host_only'); return; }
      if (room.started || room.players.some(player => !player?.peer || !player.ready)) { fail(peer, 'not_all_ready'); return; }
      room.started = true;
      broadcast(room, { type: 'started', room: metadata(room) });
      announceRoom(room); return;
    }
    if (!room.started) { fail(peer, 'match_not_started'); return; }
    if (room.paused) { fail(peer, 'match_paused', 'A player disconnected. Start a new room; automatic restore is unavailable.'); return; }
    if (['state', 'combat_state', 'combat_end'].includes(type) && peer.slot !== 0) { fail(peer, 'host_only'); return; }
    if (type === 'state') {
      if (!integer(message.revision, 0, Number.MAX_SAFE_INTEGER) || message.revision < room.revision
          || (!room.snapshot && message.revision !== 0) || !plain(message.state)
          || !integer(message.turn, -1, room.capacity - 1)) { fail(peer, 'invalid_state'); return; }
      let combat = null;
      if (message.combat !== null && message.combat !== undefined) {
        const players = message.combat?.players;
        if (!plain(message.combat) || !Array.isArray(players) || players.length !== 2 || players[0] === players[1]
            || players.some(slot => !integer(slot, 0, room.capacity - 1) || !room.players[slot]?.peer)) { fail(peer, 'invalid_combat'); return; }
        combat = { players: [...players] };
      }
      room.revision = message.revision;
      room.combat = combat;
      room.pendingAction = false;
      room.snapshot = { type: 'state', sender: 0, revision: message.revision, state: message.state, turn: message.turn, combat };
      broadcast(room, room.snapshot, peer); return;
    }
    if (!room.snapshot) { fail(peer, 'state_not_initialized'); return; }
    if (type === 'action') {
      if (!['move', 'pass'].includes(message.kind) || !integer(message.revision, 0, Number.MAX_SAFE_INTEGER)) { fail(peer, 'invalid_action'); return; }
      if (message.revision !== room.revision) { fail(peer, 'stale_revision'); return; }
      if (room.snapshot.turn !== peer.slot) { fail(peer, 'not_your_turn'); return; }
      if (room.combat) { fail(peer, 'combat_in_progress'); return; }
      if (room.pendingAction) { fail(peer, 'action_pending'); return; }
      if (message.kind === 'move' && (!integer(message.id, -1, 1000000) || !integer(message.x, 0, 31) || !integer(message.y, 0, 31))) { fail(peer, 'invalid_action'); return; }
      room.pendingAction = true;
      send(room.players[0].peer, { type: 'action', sender: peer.slot, revision: message.revision, kind: message.kind,
        id: message.kind === 'move' ? message.id : -1, x: message.kind === 'move' ? message.x : -1, y: message.kind === 'move' ? message.y : -1 });
      return;
    }
    if (type === 'combat_input') {
      if (!room.combat || !room.combat.players.includes(peer.slot)) { fail(peer, 'not_combat_participant'); return; }
      if (!plain(message.input) || Buffer.byteLength(JSON.stringify(message.input)) > 8192) { fail(peer, 'invalid_combat_input'); return; }
      send(room.players[0].peer, { type: 'combat_input', sender: peer.slot, input: message.input }); return;
    }
    if (type === 'combat_state') {
      if (!room.combat || !plain(message.state)) { fail(peer, 'invalid_combat_state'); return; }
      broadcast(room, { type: 'combat_state', sender: 0, state: message.state }, peer); return;
    }
    if (type === 'combat_end') {
      if (!room.combat || !plain(message.result)) { fail(peer, 'invalid_combat_end'); return; }
      room.combat = null;
      broadcast(room, { type: 'combat_end', sender: 0, result: message.result }, peer); return;
    }
  }

  const mime = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.json': 'application/json',
    '.css': 'text/css; charset=utf-8', '.wasm': 'application/wasm', '.bin': 'application/octet-stream', '.pck': 'application/octet-stream',
    '.png': 'image/png', '.svg': 'image/svg+xml', '.ico': 'image/x-icon', '.ttf': 'font/ttf', '.txt': 'text/plain; charset=utf-8' };
  const server = http.createServer(async (req, res) => {
    res.setHeader('X-Content-Type-Options', 'nosniff');
    if (!['GET', 'HEAD'].includes(req.method)) { res.writeHead(405); res.end(); return; }
    let pathname;
    try { pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname); } catch { res.writeHead(400); res.end(); return; }
    if (pathname === '/health') {
      res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
      res.end(req.method === 'HEAD' ? undefined : JSON.stringify({ ok: true, rooms: rooms.size })); return;
    }
    if (pathname === '/rooms') { res.writeHead(426, { Upgrade: 'websocket' }); res.end('WebSocket required'); return; }
    if (pathname.includes('\0') || pathname.includes('\\')) { res.writeHead(400); res.end(); return; }
    const candidate = path.resolve(staticRoot, '.' + (pathname === '/' ? '/index.html' : pathname));
    try {
      const [realRoot, realFile] = await Promise.all([fs.promises.realpath(staticRoot), fs.promises.realpath(candidate)]);
      if (!realFile.startsWith(realRoot + path.sep)) throw new Error('outside root');
      const stat = await fs.promises.stat(realFile);
      if (!stat.isFile()) throw new Error('not a file');
      res.writeHead(200, { 'Content-Type': mime[path.extname(realFile)] ?? 'application/octet-stream', 'Content-Length': stat.size,
        'Cache-Control': 'no-cache' });
      if (req.method === 'HEAD') res.end();
      else fs.createReadStream(realFile).on('error', () => res.destroy()).pipe(res);
    } catch { res.writeHead(404); res.end('Not found'); }
  });
  server.requestTimeout = 15000;
  server.headersTimeout = 10000;

  server.on('upgrade', (req, socket, head) => {
    const reject = (status, text) => socket.end(`HTTP/1.1 ${status} ${text}\r\nConnection: close\r\nContent-Length: 0\r\n\r\n`);
    const ip = socket.remoteAddress;
    const origin = req.headers.origin;
    const sameOrigin = origin === `http://${req.headers.host}` || origin === `https://${req.headers.host}`;
    if (shuttingDown || req.url !== '/rooms') { reject(404, 'Not Found'); return; }
    if (origin && !(allowedOrigins.length ? allowedOrigins.includes(origin) : sameOrigin)) { reject(403, 'Forbidden'); return; }
    if (peers.size >= maxPeers || [...peers].filter(p => p.ip === ip).length >= maxPeersPerIP) { reject(503, 'Busy'); return; }
    const key = req.headers['sec-websocket-key'];
    if (req.method !== 'GET' || String(req.headers.upgrade).toLowerCase() !== 'websocket'
        || !String(req.headers.connection).toLowerCase().split(/\s*,\s*/u).includes('upgrade')
        || req.headers['sec-websocket-version'] !== '13' || typeof key !== 'string'
        || !/^[A-Za-z0-9+/]{22}==$/u.test(key) || Buffer.from(key, 'base64').length !== 16) { reject(400, 'Bad Request'); return; }
    const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
    socket.write(`HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ${accept}\r\n\r\n`);
    socket.setNoDelay(true);
    const peer = { socket, ip, room: null, slot: null, closed: false, alive: true, lastActivity: Date.now(),
      tokens: 360, tokenTime: Date.now(), lobbyTokens: 20, lobbyTime: Date.now(), close: null };
    peers.add(peer);
    let buffer = Buffer.alloc(0), fragments = [], fragmentBytes = 0, fragmented = false;
    function cleanup() {
      if (peer.closed) return;
      peer.closed = true; peers.delete(peer); depart(peer);
    }
    peer.close = (code = 1000, reason = '') => {
      if (peer.closed) return;
      const body = Buffer.alloc(2); body.writeUInt16BE(code);
      socket.end(frame(8, Buffer.concat([body, Buffer.from(reason).subarray(0, 120)])));
      cleanup();
      const timer = setTimeout(() => socket.destroy(), 200); timer.unref();
    };
    socket.on('close', cleanup);
    socket.on('error', cleanup);
    function onData(chunk) {
      if (peer.closed) return;
      if (buffer.length + chunk.length > MAX_MESSAGE_BYTES * 2 + 64) { peer.close(1009, 'Receive buffer limit'); return; }
      buffer = Buffer.concat([buffer, chunk]);
      while (buffer.length >= 2 && !peer.closed) {
        const first = buffer[0], second = buffer[1], opcode = first & 15, fin = Boolean(first & 128);
        if ((first & 112) || !(second & 128) || ![0, 1, 2, 8, 9, 10].includes(opcode)) { peer.close(1002, 'Invalid frame'); return; }
        let length = second & 127, offset = 2;
        if (length === 126) { if (buffer.length < 4) return; length = buffer.readUInt16BE(2); offset = 4; }
        else if (length === 127) {
          if (buffer.length < 10) return;
          const large = buffer.readBigUInt64BE(2);
          if (large > BigInt(MAX_MESSAGE_BYTES)) { peer.close(1009, 'Message too large'); return; }
          length = Number(large); offset = 10;
        }
        if (length > MAX_MESSAGE_BYTES || fragmentBytes + length > MAX_MESSAGE_BYTES) { peer.close(1009, 'Message too large'); return; }
        if (opcode >= 8 && (!fin || length > 125)) { peer.close(1002, 'Invalid control frame'); return; }
        if (buffer.length < offset + 4 + length) return;
        const mask = buffer.subarray(offset, offset + 4);
        const payload = Buffer.from(buffer.subarray(offset + 4, offset + 4 + length));
        for (let i = 0; i < length; i++) payload[i] ^= mask[i & 3];
        buffer = buffer.subarray(offset + 4 + length);
        if (opcode === 8) { peer.close(1000, 'Closed'); return; }
        if (opcode === 9) { socket.write(frame(10, payload)); continue; }
        if (opcode === 10) { peer.alive = true; continue; }
        if (opcode === 2) { peer.close(1003, 'Text JSON required'); return; }
        if ((opcode === 0 && !fragmented) || (opcode === 1 && fragmented)) { peer.close(1002, 'Invalid continuation'); return; }
        if (opcode === 1 && !fin) fragmented = true;
        fragments.push(payload); fragmentBytes += payload.length;
        if (!fin) continue;
        const complete = Buffer.concat(fragments, fragmentBytes);
        fragments = []; fragmentBytes = 0; fragmented = false;
        let message;
        try { message = JSON.parse(utf8.decode(complete)); }
        catch { fail(peer, 'invalid_json', 'Valid UTF-8 JSON required'); continue; }
        handle(peer, message);
      }
    }
    socket.on('data', onData);
    send(peer, { type: 'hello', protocol: 1, max_message_bytes: MAX_MESSAGE_BYTES, reconnect: false });
    if (head.length) onData(head);
  });
  const sweep = setInterval(() => {
    const now = Date.now();
    for (const room of rooms.values()) if (now - room.touched > idleMs) closeRoom(room, 'idle_expired');
    for (const peer of peers) {
      if (!peer.room && now - peer.lastActivity > 60000) { peer.close(1000, 'Idle connection'); continue; }
      if (!peer.alive) { peer.close(1001, 'Heartbeat timeout'); continue; }
      peer.alive = false;
      peer.socket.write(frame(9));
    }
  }, options.sweepMs ?? 20000);
  sweep.unref();
  return { server,
    listen(port = 8787, host = '127.0.0.1') { return new Promise((resolve, reject) => { server.once('error', reject); server.listen(port, host, () => { server.off('error', reject); resolve(server.address()); }); }); },
    async close() {
      shuttingDown = true; clearInterval(sweep);
      for (const peer of [...peers]) { peer.close(1001, 'Server shutdown'); peer.socket.destroy(); }
      await new Promise(resolve => server.close(resolve));
    }
  };
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const service = createRoomServer({
    maxRooms: Number(process.env.ROOM_MAX_ROOMS) || 128,
    idleMs: (Number(process.env.ROOM_IDLE_MINUTES) || 60) * 60000,
    allowedOrigins: (process.env.ROOM_ALLOWED_ORIGINS ?? '').split(',').map(s => s.trim()).filter(Boolean)
  });
  const address = await service.listen(Number(process.env.PORT) || 8787, process.env.HOST || '127.0.0.1');
  console.log(`OVERDRIVE: RECTOR room server: http://${address.address}:${address.port}  WebSocket /rooms`);
  process.once('SIGTERM', async () => { await service.close(); });
  process.once('SIGINT', async () => { await service.close(); });
}
