// Трансляция файла: видео играет у одного человека и идёт остальным напрямую из его браузера (WebRTC).
// Firebase здесь только «знакомит» браузеры: передаёт короткие служебные сообщения (offer/answer/ICE).
// Путь в базе: rooms/{room}/rtc/{hostUid}/{viewerUid} = { sid, offer, answer, hc:{}, vc:{} }

import { ref, set, update, push, onValue, onDisconnect, remove } from "https://www.gstatic.com/firebasejs/10.14.1/firebase-database.js";

/* global extraIceServers */
function iceServers() {
  const base = [{ urls: ["stun:stun.l.google.com:19302", "stun:stun1.l.google.com:19302"] }];
  const extra = (typeof extraIceServers !== "undefined" && Array.isArray(extraIceServers)) ? extraIceServers : [];
  return base.concat(extra.filter(s => s && s.urls));
}
const rid = () => Math.random().toString(36).slice(2, 10);
const MAX_BITRATE = 4_000_000; // ~4 Мбит/с на зрителя

// ---------------------------------------------------------------- host
export function startHost({ db, room, uid, video, onViewers }) {
  const base = ref(db, `rooms/${room}/rtc/${uid}`);
  const peers = new Map(); // viewerUid -> { sid, pc, vcSeen:Set, answered }
  let stream = null, stopped = false;

  try { onDisconnect(base).remove(); } catch {}

  function getStream() {
    if (stream) return stream;
    const cap = video.captureStream || video.mozCaptureStream;
    if (!cap) throw new Error("Этот браузер не умеет транслировать видео. Откройте сайт в Chrome или Edge на компьютере.");
    stream = cap.call(video);
    return stream;
  }
  async function waitTracks() {
    const s = getStream();
    for (let i = 0; i < 50 && s.getTracks().length === 0; i++) await new Promise(r => setTimeout(r, 100));
    return s;
  }

  async function connect(viewer, sid) {
    const old = peers.get(viewer);
    if (old) try { old.pc.close(); } catch {}
    const pc = new RTCPeerConnection({ iceServers: iceServers() });
    const p = { sid, pc, vcSeen: new Set(), answered: false };
    peers.set(viewer, p);
    const node = `rooms/${room}/rtc/${uid}/${viewer}`;
    pc.onicecandidate = e => { if (e.candidate && peers.get(viewer) === p) push(ref(db, `${node}/hc`), e.candidate.toJSON()).catch(() => {}); };
    pc.onconnectionstatechange = () => { if (/failed|closed/.test(pc.connectionState) && peers.get(viewer) === p) { peers.delete(viewer); onViewers?.(peers.size); } else onViewers?.(countConnected()); };
    const s = await waitTracks();
    for (const t of s.getTracks()) pc.addTrack(t, s);
    // when the video changes tracks (e.g. new audio track), keep senders up to date
    s.onaddtrack = e => { try { pc.addTrack(e.track, s); } catch {} };
    const offer = await pc.createOffer();
    await pc.setLocalDescription(offer);
    for (const sender of pc.getSenders()) {
      if (sender.track?.kind !== "video") continue;
      try { const prm = sender.getParameters(); prm.encodings = prm.encodings?.length ? prm.encodings : [{}]; prm.encodings[0].maxBitrate = MAX_BITRATE; await sender.setParameters(prm); } catch {}
    }
    if (peers.get(viewer) !== p || stopped) return;
    await update(ref(db, node), { offer: { sid, type: offer.type, sdp: offer.sdp } });
  }
  const countConnected = () => [...peers.values()].filter(p => p.pc.connectionState === "connected").length;

  const unsub = onValue(base, snap => {
    if (stopped) return;
    const all = snap.val() || {};
    for (const [viewer, node] of Object.entries(all)) {
      if (!node || typeof node.sid !== "string") continue;
      let p = peers.get(viewer);
      if (!p || p.sid !== node.sid) { connect(viewer, node.sid).catch(() => {}); continue; }
      if (!p.answered && node.answer && node.answer.sid === p.sid && typeof node.answer.sdp === "string") {
        p.answered = true;
        p.remote = p.pc.setRemoteDescription({ type: "answer", sdp: node.answer.sdp }).catch(() => {});
      }
      if (p.answered && node.vc) for (const [k, c] of Object.entries(node.vc)) {
        if (p.vcSeen.has(k)) continue; p.vcSeen.add(k);
        p.remote.then(() => p.pc.addIceCandidate(c)).catch(() => {});
      }
    }
    for (const viewer of [...peers.keys()]) if (!all[viewer]) { try { peers.get(viewer).pc.close(); } catch {} peers.delete(viewer); }
    onViewers?.(countConnected());
  });

  return {
    stop() {
      stopped = true; unsub();
      for (const p of peers.values()) try { p.pc.close(); } catch {}
      peers.clear();
      try { onDisconnect(base).cancel(); } catch {}
      remove(base).catch(() => {});
    }
  };
}

// ---------------------------------------------------------------- viewer
export function startViewer({ db, room, uid, host, video, onStatus }) {
  const node = `rooms/${room}/rtc/${host}/${uid}`;
  let pc = null, sid = null, unsub = null, stopped = false, retry = null, hcSeen = new Set(), answered = false, remote = null;

  try { onDisconnect(ref(db, node)).remove(); } catch {}

  function begin() {
    if (stopped) return;
    clearTimeout(retry);
    try { pc?.close(); } catch {}
    unsub?.();
    sid = rid(); answered = false; hcSeen = new Set();
    pc = new RTCPeerConnection({ iceServers: iceServers() });
    const my = pc;
    pc.ontrack = e => {
      const s = e.streams[0] || new MediaStream([e.track]);
      if (video.srcObject !== s) video.srcObject = s;
      onStatus?.("stream");
    };
    pc.onicecandidate = e => { if (e.candidate && pc === my) push(ref(db, `${node}/vc`), e.candidate.toJSON()).catch(() => {}); };
    pc.onconnectionstatechange = () => {
      if (pc !== my) return;
      const st = pc.connectionState;
      if (st === "connected") onStatus?.("connected");
      else if (st === "failed") { onStatus?.("failed"); retry = setTimeout(begin, 4000); }
      else if (st === "disconnected") { onStatus?.("reconnecting"); retry = setTimeout(() => { if (pc === my && pc.connectionState !== "connected") begin(); }, 6000); }
    };
    onStatus?.("connecting");
    set(ref(db, node), { sid, at: Date.now() }).catch(() => onStatus?.("failed"));
    unsub = onValue(ref(db, node), async snap => {
      const n = snap.val() || {};
      if (stopped || pc !== my) return;
      if (!answered && n.offer && n.offer.sid === sid && typeof n.offer.sdp === "string") {
        answered = true;
        remote = pc.setRemoteDescription({ type: "offer", sdp: n.offer.sdp });
        try {
          await remote;
          const ans = await pc.createAnswer();
          await pc.setLocalDescription(ans);
          await update(ref(db, node), { answer: { sid, type: ans.type, sdp: ans.sdp } });
        } catch { onStatus?.("failed"); }
      }
      if (answered && n.hc) for (const [k, c] of Object.entries(n.hc)) {
        if (hcSeen.has(k)) continue; hcSeen.add(k);
        remote.then(() => my.addIceCandidate(c)).catch(() => {});
      }
    });
    // no answer from the host in time: try again
    retry = setTimeout(() => { if (pc === my && !answered) { onStatus?.("nohost"); begin(); } }, 15000);
  }
  begin();

  return {
    reconnect: begin,
    stop() {
      stopped = true; clearTimeout(retry); unsub?.();
      try { pc?.close(); } catch {}
      try { onDisconnect(ref(db, node)).cancel(); } catch {}
      remove(ref(db, node)).catch(() => {});
    }
  };
}
