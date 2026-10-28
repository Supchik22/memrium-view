//! Memrium View: an image viewer built on Chebrium. Pictures are decoded on a worker thread (the neighbours too, so
//! the next one is already there), zoom glides towards the pointer, and the controls fade away when you stop moving.

use chebrium::app::{self, App, Config, Decorations, Host, Waker};
use chebrium::appmenu::{Item, Menu};
use chebrium::chrome;
use chebrium::i18n::{tr, trf};
use chebrium::theme::{Appearance, Decor};
use chebrium::draw::Align;
use chebrium::input::{Key, KeyMods};
use chebrium::picture::Pic;
use chebrium::style::Style;
use chebrium::ui::{inside, Ui};
use memrium_de::fsops;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::Arc;
use std::time::{Duration, Instant};

const BG: [f32; 3] = [0.075, 0.078, 0.09];
const EXTS: [&str; 11] = ["png", "jpg", "jpeg", "webp", "gif", "bmp", "tif", "tiff", "ico", "svg", "jfif"];
const K_ZOOM: u64 = 70_000;
const K_PAN_X: u64 = 70_001;
const K_PAN_Y: u64 = 70_002;
const K_UI: u64 = 70_003;
const K_FADE: u64 = 70_004;
const IDLE: Duration = Duration::from_millis(2500);
/// decoded pictures kept around (the current one and its neighbours), by memory
const CACHE_BYTES: usize = 192 << 20;

fn is_image(p: &Path) -> bool {
    p.extension().and_then(|e| e.to_str()).is_some_and(|e| EXTS.contains(&e.to_ascii_lowercase().as_str()))
}

/// Case-insensitive ordering where numbers compare as numbers (`img2` before `img10`).
fn natural(a: &str, b: &str) -> std::cmp::Ordering {
    let (a, b) = (a.to_lowercase(), b.to_lowercase());
    let (mut ai, mut bi) = (a.chars().peekable(), b.chars().peekable());
    loop {
        match (ai.peek().copied(), bi.peek().copied()) {
            (None, None) => return std::cmp::Ordering::Equal,
            (None, _) => return std::cmp::Ordering::Less,
            (_, None) => return std::cmp::Ordering::Greater,
            (Some(x), Some(y)) if x.is_ascii_digit() && y.is_ascii_digit() => {
                let (mut n, mut m) = (String::new(), String::new());
                while let Some(c) = ai.peek().copied().filter(char::is_ascii_digit) {
                    n.push(c);
                    ai.next();
                }
                while let Some(c) = bi.peek().copied().filter(char::is_ascii_digit) {
                    m.push(c);
                    bi.next();
                }
                let (n, m) = (n.trim_start_matches('0'), m.trim_start_matches('0'));
                let o = n.len().cmp(&m.len()).then_with(|| n.cmp(m));
                if o != std::cmp::Ordering::Equal {
                    return o;
                }
            }
            (Some(x), Some(y)) => {
                if x != y {
                    return x.cmp(&y);
                }
                ai.next();
                bi.next();
            }
        }
    }
}

fn pictures_in(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir).into_iter().flatten().flatten().map(|e| e.path()).filter(|p| p.is_file() && is_image(p)).collect();
    v.sort_by(|a, b| natural(&a.file_name().unwrap_or_default().to_string_lossy(), &b.file_name().unwrap_or_default().to_string_lossy()));
    v
}

/// Decode a file (turned upright by its EXIF orientation); SVG is rendered at a size that stays sharp when zoomed.
fn decode(path: &Path) -> Result<Pic, String> {
    if path.extension().and_then(|e| e.to_str()).is_some_and(|e| e.eq_ignore_ascii_case("svg")) {
        let data = std::fs::read(path).map_err(|e| e.to_string())?;
        let tree = resvg::usvg::Tree::from_data(&data, &resvg::usvg::Options::default()).map_err(|e| e.to_string())?;
        let size = tree.size();
        let k = (2048.0 / size.width().max(size.height())).clamp(0.01, 16.0);
        let (w, h) = ((size.width() * k).ceil().max(1.0) as u32, (size.height() * k).ceil().max(1.0) as u32);
        let mut pix = resvg::tiny_skia::Pixmap::new(w, h).ok_or("empty svg")?;
        resvg::render(&tree, resvg::tiny_skia::Transform::from_scale(k, k), &mut pix.as_mut());
        // tiny-skia gives premultiplied RGBA; the canvas wants premultiplied BGRA
        let mut data = pix.take();
        for p in data.chunks_exact_mut(4) {
            p.swap(0, 2);
        }
        let opaque = data.chunks_exact(4).all(|p| p[3] == 255);
        return Ok(Pic::from_bgra(w, h, data, opaque, true));
    }
    use image::ImageDecoder;
    let mut dec = image::ImageReader::open(path).map_err(|e| e.to_string())?.with_guessed_format().map_err(|e| e.to_string())?.into_decoder().map_err(|e| e.to_string())?;
    let orientation = dec.orientation().unwrap_or(image::metadata::Orientation::NoTransforms);
    let mut img = image::DynamicImage::from_decoder(dec).map_err(|e| e.to_string())?;
    img.apply_orientation(orientation);
    let rgba = img.to_rgba8();
    Ok(Pic::from_rgba(rgba.width(), rgba.height(), rgba.as_raw()))
}

struct Loaded {
    path: PathBuf,
    pic: Result<Pic, String>,
}

#[derive(Clone, Copy, PartialEq)]
enum Zoom {
    Fit,
    Actual,
    Custom,
}

struct Viewer {
    files: Vec<PathBuf>,
    index: usize,
    cache: HashMap<PathBuf, Arc<Pic>>,
    /// least recently shown first
    order: Vec<PathBuf>,
    pending: Vec<PathBuf>,
    failed: HashMap<PathBuf, String>,
    tx: Sender<Loaded>,
    rx: Receiver<Loaded>,
    waker: Option<Waker>,
    // the view
    mode: Zoom,
    /// where the view is heading: scale (screen px per picture px) and the pan of the picture's centre from the middle of the window
    zoom: f32,
    pan: [f32; 2],
    /// the picture shown last frame, to start a new one without a glide
    shown: Option<u64>,
    drag: Option<([f32; 2], [f32; 2])>,
    last_move: Instant,
    last_mouse: [f32; 2],
    sleeper: Arc<AtomicBool>,
    info: bool,
    fullscreen: bool,
    title: String,
    note: String,
    /// the right-click menu: where it was opened
    ctx: Option<[f32; 2]>,
}

impl Viewer {
    fn new(arg: Option<PathBuf>) -> Viewer {
        let (tx, rx) = channel();
        let (files, index) = match arg {
            Some(p) if p.is_dir() => (pictures_in(&p), 0),
            Some(p) => {
                let dir = p.parent().map(Path::to_path_buf).unwrap_or_else(|| PathBuf::from("."));
                let mut files = pictures_in(if dir.as_os_str().is_empty() { Path::new(".") } else { &dir });
                // a file with an unusual extension is still opened when it was named
                if !files.contains(&p) {
                    files.push(p.clone());
                }
                let i = files.iter().position(|f| f == &p).unwrap_or(0);
                (files, i)
            }
            None => (pictures_in(&fsops::home().join("Pictures")), 0),
        };
        let mut v = Viewer {
            files,
            index,
            cache: HashMap::new(),
            order: Vec::new(),
            pending: Vec::new(),
            failed: HashMap::new(),
            tx,
            rx,
            waker: None,
            mode: Zoom::Fit,
            zoom: 1.0,
            pan: [0.0; 2],
            shown: None,
            drag: None,
            last_move: Instant::now(),
            last_mouse: [-1.0; 2],
            sleeper: Arc::new(AtomicBool::new(false)),
            info: false,
            fullscreen: false,
            title: String::new(),
            note: String::new(),
            ctx: None,
        };
        v.want_around();
        v
    }

    fn current(&self) -> Option<&PathBuf> {
        self.files.get(self.index)
    }

    /// Start decoding the current picture and its neighbours.
    fn want_around(&mut self) {
        let n = self.files.len();
        if n == 0 {
            return;
        }
        for d in [0usize, 1, n - 1] {
            let p = self.files[(self.index + d) % n].clone();
            if self.cache.contains_key(&p) || self.pending.contains(&p) || self.failed.contains_key(&p) {
                continue;
            }
            self.pending.push(p.clone());
            let (tx, waker) = (self.tx.clone(), self.waker.clone());
            std::thread::spawn(move || {
                let pic = decode(&p);
                let _ = tx.send(Loaded { path: p, pic });
                if let Some(w) = waker {
                    w.wake();
                }
            });
        }
    }

    /// Take what the decoder threads have finished, and keep the cache within its budget.
    fn collect(&mut self) {
        while let Ok(done) = self.rx.try_recv() {
            self.pending.retain(|p| p != &done.path);
            match done.pic {
                Ok(pic) => {
                    self.order.retain(|p| p != &done.path);
                    self.order.push(done.path.clone());
                    self.cache.insert(done.path, Arc::new(pic));
                }
                Err(e) => {
                    self.failed.insert(done.path, e);
                }
            }
        }
        let mut total: usize = self.cache.values().map(|p| p.bytes()).sum();
        let cur = self.current().cloned();
        while total > CACHE_BYTES && self.order.len() > 1 {
            let Some(i) = self.order.iter().position(|p| Some(p) != cur.as_ref()) else { break };
            let p = self.order.remove(i);
            if let Some(pic) = self.cache.remove(&p) {
                total -= pic.bytes();
            }
        }
    }

    fn go(&mut self, delta: isize) {
        let n = self.files.len() as isize;
        if n == 0 {
            return;
        }
        self.index = (self.index as isize + delta).rem_euclid(n) as usize;
        self.mode = Zoom::Fit;
        self.pan = [0.0; 2];
        self.want_around();
    }

    fn jump(&mut self, to: usize) {
        if to < self.files.len() {
            self.index = to;
            self.mode = Zoom::Fit;
            self.pan = [0.0; 2];
            self.want_around();
        }
    }

    fn fit_scale(&self, pic: &Pic, view: [f32; 2]) -> f32 {
        // small pictures are shown at their own size rather than blown up
        (view[0] / pic.w as f32).min(view[1] / pic.h as f32).min(1.0)
    }

    /// Zoom by `factor` keeping the picture point under `at` (relative to the window's middle) where it is.
    fn zoom_at(&mut self, factor: f32, at: [f32; 2], cur_scale: f32) {
        let new = (cur_scale * factor).clamp(0.02, 64.0);
        let k = new / cur_scale;
        self.pan = [(self.pan[0] - at[0]) * k + at[0], (self.pan[1] - at[1]) * k + at[1]];
        self.zoom = new;
        self.mode = Zoom::Custom;
    }

    fn rotate(&mut self, turns: u32) {
        let Some(p) = self.current().cloned() else { return };
        if let Some(pic) = self.cache.get(&p) {
            let r = Arc::new(pic.rotated(turns));
            self.cache.insert(p, r);
            self.pan = [0.0; 2];
            if self.mode == Zoom::Custom {
                self.mode = Zoom::Fit;
            }
        }
    }

    fn delete(&mut self) {
        let Some(p) = self.current().cloned() else { return };
        match fsops::trash(&p) {
            Ok(_) => {
                self.note = trf("{} moved to the Trash", &[p.file_name().unwrap_or_default().to_string_lossy().to_string()]);
                self.files.remove(self.index);
                self.cache.remove(&p);
                self.order.retain(|q| q != &p);
                if self.index >= self.files.len() {
                    self.index = self.files.len().saturating_sub(1);
                }
                self.pan = [0.0; 2];
                self.mode = Zoom::Fit;
                self.want_around();
            }
            Err(e) => self.note = trf("Could not move to the Trash: {}", &[e.to_string()]),
        }
    }

    /// Keep the controls up for a moment after the pointer moved; wake the program once that moment is over.
    fn touch(&mut self) {
        self.last_move = Instant::now();
        if !self.sleeper.swap(true, Ordering::SeqCst) {
            let (flag, waker) = (self.sleeper.clone(), self.waker.clone());
            std::thread::spawn(move || {
                std::thread::sleep(IDLE + Duration::from_millis(80));
                flag.store(false, Ordering::SeqCst);
                if let Some(w) = waker {
                    w.wake();
                }
            });
        }
    }
}

fn icon_button(ui: &mut Ui<'_>, cx: f32, cy: f32, icon: &str, alpha: f32, on: bool) -> bool {
    let r = [cx - 17.0, cy - 17.0, 34.0, 34.0];
    let hov = alpha > 0.3 && ui.hit(r);
    let key = ui.id() * 64;
    let wash = ui.ease(key, if hov { 1.0 } else { 0.0 }, 22.0);
    ui.fill(r, 17.0, if on { ui.accent } else { [1.0; 3] }, (if on { 0.35 } else { 0.0 } + 0.16 * wash) * alpha);
    ui.glyph(cx, cy, 18.0, icon, [1.0; 3], 0.95 * alpha);
    ui.click && hov && alpha > 0.3
}

fn human(bytes: u64) -> String {
    fsops::human_size(bytes)
}

impl App for Viewer {
    fn start(&mut self, waker: Waker) {
        self.waker = Some(waker);
        // pictures requested before the runtime was up still need to wake it
        self.pending.clear();
        self.want_around();
    }

    // a viewer shows pictures on a dark, quiet ground whatever the theme; the accent and the window controls follow it
    fn style(&self, look: &Appearance) -> Style {
        Style::new(true, look.accent)
    }

    fn background(&self, _look: &Appearance) -> ([f32; 3], f32) {
        (BG, 1.0)
    }

    fn menus(&self) -> Vec<Menu> {
        vec![
            Menu::new("File", vec![Item::new(1, "Move to Trash").key("Delete"), Item::sep(), Item::new(2, "Close").key("Q")]),
            Menu::new("Edit", vec![Item::new(30, "Copy Picture").key("Ctrl+C").enabled(self.current().is_some()), Item::new(31, "Copy File Path").enabled(self.current().is_some())]),
            Menu::new(
                "View",
                vec![
                    Item::new(10, "Zoom In").key("+"),
                    Item::new(11, "Zoom Out").key("-"),
                    Item::new(12, "Fit to Window").key("0"),
                    Item::new(13, "Actual Size").key("1"),
                    Item::sep(),
                    Item::new(14, "Rotate Right").key("R"),
                    Item::new(15, "Rotate Left").key("Shift+R"),
                    Item::sep(),
                    Item::new(16, "Full Screen").key("F").checked(self.fullscreen),
                    Item::new(17, "Show Info").key("I").checked(self.info),
                ],
            ),
            Menu::new("Go", vec![Item::new(20, "Next Picture").key("→"), Item::new(21, "Previous Picture").key("←"), Item::new(22, "First Picture").key("Home"), Item::new(23, "Last Picture").key("End")]),
        ]
    }

    fn raw_pointer(&mut self, event: &app::PointerEvt, _mods: &app::Modifiers, host: &mut Host) -> bool {
        // the right button opens the menu where the pointer is
        if let app::PointerKind::Press { button: 0x111, .. } = event.kind {
            self.ctx = if self.current().is_some() { Some(event.pos) } else { None };
            host.redraw = true;
            return true;
        }
        false
    }

    fn menu_action(&mut self, id: u32, host: &mut Host) {
        let key = match id {
            1 => Key::Delete,
            2 => Key::Char('q'),
            10 => Key::Char('+'),
            11 => Key::Char('-'),
            12 => Key::Char('0'),
            13 => Key::Char('1'),
            14 => Key::Char('r'),
            15 => Key::Char('R'),
            16 => Key::Char('f'),
            17 => Key::Char('i'),
            20 => Key::Right,
            21 => Key::Left,
            22 => Key::Home,
            23 => Key::End,
            30 => return self.copy_picture(host),
            31 => return self.copy_path(host),
            _ => return,
        };
        self.key(key, KeyMods::default(), host);
    }

    fn key(&mut self, key: Key, mods: KeyMods, host: &mut Host) {
        host.redraw = true;
        self.touch();
        if mods.ctrl && key == Key::Char('c') {
            return self.copy_picture(host);
        }
        match key {
            Key::Right | Key::Down | Key::PageDown | Key::Char(' ') => self.go(1),
            Key::Left | Key::Up | Key::PageUp | Key::Backspace => self.go(-1),
            Key::Home => self.jump(0),
            Key::End => self.jump(self.files.len().saturating_sub(1)),
            Key::Delete => self.delete(),
            Key::Esc => {
                if self.fullscreen {
                    self.fullscreen = false;
                    host.fullscreen = Some(false);
                } else {
                    host.quit = true;
                }
            }
            Key::Char('q') => host.quit = true,
            Key::Char('+') | Key::Char('=') => self.zoom_step(1.25),
            Key::Char('-') | Key::Char('_') => self.zoom_step(0.8),
            Key::Char('0') => {
                self.mode = Zoom::Fit;
                self.pan = [0.0; 2];
            }
            Key::Char('1') => {
                self.mode = Zoom::Actual;
                self.pan = [0.0; 2];
            }
            Key::Char('r') if !mods.ctrl => self.rotate(1),
            Key::Char('R') | Key::Char('l') => self.rotate(3),
            Key::Char('i') => self.info = !self.info,
            _ => {}
        }
        if key == Key::Char('f') {
            self.fullscreen = !self.fullscreen;
            host.fullscreen = Some(self.fullscreen);
        }
    }

    fn draw(&mut self, ui: &mut Ui<'_>, size: [f32; 2], host: &mut Host) {
        let [w, h] = size;
        let resizing = chrome::resize_borders(ui, host, size);
        self.collect();
        // pointer movement keeps the controls up
        if (ui.mouse[0] - self.last_mouse[0]).abs() + (ui.mouse[1] - self.last_mouse[1]).abs() > 0.5 || ui.click {
            self.last_mouse = ui.mouse;
            self.touch();
        }
        let path = self.current().cloned();
        let pic = path.as_ref().and_then(|p| self.cache.get(p)).cloned();
        let controls_on = self.last_move.elapsed() < IDLE || self.files.is_empty() || pic.is_none();
        let ui_a = ui.ease(K_UI, if controls_on { 1.0 } else { 0.0 }, 9.0);

        // ---- the picture
        if let Some(pic) = &pic {
            let view = [w, h];
            let fit = self.fit_scale(pic, view);
            if self.shown != Some(pic.id) {
                // a new picture appears where it belongs, fading in
                self.shown = Some(pic.id);
                ui.snap(K_FADE, 0.0);
                let s = match self.mode {
                    Zoom::Actual => 1.0,
                    _ => fit,
                };
                ui.snap(K_ZOOM, s.ln());
                ui.snap(K_PAN_X, self.pan[0]);
                ui.snap(K_PAN_Y, self.pan[1]);
            }
            // the scale the view is heading for
            let target = match self.mode {
                Zoom::Fit => fit,
                Zoom::Actual => 1.0,
                Zoom::Custom => self.zoom,
            };
            let cur = ui.ease(K_ZOOM, target.ln(), 14.0).exp();
            // wheel: zoom towards the pointer; the pointer must be over the picture area
            if ui.scroll != 0.0 {
                let at = [ui.mouse[0] - w / 2.0, ui.mouse[1] - h / 2.0];
                self.zoom_at((-ui.scroll * 0.0016).exp(), at, if self.mode == Zoom::Custom { self.zoom } else { target });
            }
            // drag to pan (a press that began on the picture, not on the controls)
            let over_controls = ui.mouse[1] > h - 90.0 && inside(ui.mouse, [w / 2.0 - 250.0, h - 90.0, 500.0, 90.0]) && ui_a > 0.3;
            if ui.click && !over_controls && !resizing && ui.mouse[1] > 44.0 {
                self.drag = Some((ui.mouse, self.pan));
            }
            if !ui.held {
                self.drag = None;
            }
            if let Some((from, pan0)) = self.drag {
                if self.mode != Zoom::Custom {
                    self.zoom = target;
                    self.mode = Zoom::Custom;
                }
                self.pan = [pan0[0] + ui.mouse[0] - from[0], pan0[1] + ui.mouse[1] - from[1]];
            }
            if ui.double && !over_controls && ui.mouse[1] > 44.0 {
                let at = [ui.mouse[0] - w / 2.0, ui.mouse[1] - h / 2.0];
                if (target - 1.0).abs() > 0.01 {
                    self.zoom_at(1.0 / target, at, target);
                } else {
                    self.mode = Zoom::Fit;
                    self.pan = [0.0; 2];
                }
            }
            // keep the picture from being carried away; one smaller than the window sits in the middle
            let scale_now = if self.mode == Zoom::Custom { self.zoom } else { target };
            let (dw, dh) = (pic.w as f32 * scale_now, pic.h as f32 * scale_now);
            let lim = [((dw - w) / 2.0).max(0.0), ((dh - h) / 2.0).max(0.0)];
            self.pan = [self.pan[0].clamp(-lim[0], lim[0]), self.pan[1].clamp(-lim[1], lim[1])];
            let shown_pan = [ui.ease(K_PAN_X, self.pan[0], 16.0), ui.ease(K_PAN_Y, self.pan[1], 16.0)];
            let (sw, sh) = (pic.w as f32 * cur, pic.h as f32 * cur);
            let dest = [w / 2.0 + shown_pan[0] - sw / 2.0, h / 2.0 + shown_pan[1] - sh / 2.0, sw, sh];
            let fade = ui.ease(K_FADE, 1.0, 12.0);
            ui.picture(dest, pic, [0.0, 0.0, pic.w as f32, pic.h as f32], fade);
        } else if let Some(p) = &path {
            let msg = match self.failed.get(p) {
                Some(e) => trf("Cannot open this picture: {}", &[e.clone()]),
                None => tr("Loading…").into_owned(),
            };
            ui.text_raw(w / 2.0, h / 2.0, &msg, 15.0, false, [1.0; 3], 0.6, Align::Center);
        } else {
            ui.glyph(w / 2.0, h / 2.0 - 30.0, 54.0, "image", [1.0; 3], 0.35);
            ui.text(w / 2.0, h / 2.0 + 30.0, "No pictures here", 16.0, true, [1.0; 3], 0.7, Align::Center);
            ui.text(w / 2.0, h / 2.0 + 54.0, "Open a picture or a folder: memrium_view <file or folder>", 12.5, false, [1.0; 3], 0.45, Align::Center);
        }

        // ---- controls: a name bar at the top, a pill of buttons at the bottom, both fading away
        if ui_a > 0.01 {
            let name = path.as_ref().and_then(|p| p.file_name()).map(|n| n.to_string_lossy().to_string()).unwrap_or_default();
            ui.fill([0.0, 0.0, w, 44.0], 0.0, [0.0; 3], 0.45 * ui_a);
            // the window's own buttons in the desktop's style: on the left for macOS, on the right otherwise
            let on_button = chrome::controls(ui, host, 0.0, w, 22.0, ui_a);
            let mac = host.appearance.decor == Decor::Mac;
            let (name_x, count_x) = if mac { (96.0, w - 18.0) } else { (18.0, w - 150.0) };
            ui.text_raw(name_x, 28.0, &name, 14.0, true, [1.0; 3], 0.95 * ui_a, Align::Left);
            if !self.files.is_empty() {
                ui.text_raw(count_x, 28.0, &format!("{} / {}", self.index + 1, self.files.len()), 13.0, false, [1.0; 3], 0.7 * ui_a, Align::Right);
            }
            if !self.note.is_empty() {
                ui.text_raw(w / 2.0, 28.0, &self.note.clone(), 12.5, false, [1.0; 3], 0.7 * ui_a, Align::Center);
            }
            // a press on the bar (not on a button) moves the window; twice maximises it
            if ui.click && !on_button && !resizing && ui.mouse[1] < 44.0 && ui_a > 0.3 {
                if ui.double {
                    host.toggle_maximize = true;
                } else {
                    host.drag = true;
                }
            }
            let (px, py, pw, ph) = (w / 2.0 - 250.0, h - 70.0, 500.0, 48.0);
            ui.glass([px, py, pw, ph], 24.0, ui_a);
            let cy = py + ph / 2.0;
            let mut x = px + 30.0;
            let step = 42.0;
            if icon_button(ui, x, cy, "chevron-left", ui_a, false) {
                self.go(-1);
            }
            x += step;
            if icon_button(ui, x, cy, "chevron-right", ui_a, false) {
                self.go(1);
            }
            x += step + 6.0;
            ui.fill([x - 3.0, cy - 11.0, 1.0, 22.0], 0.0, [1.0; 3], 0.15 * ui_a);
            x += 14.0;
            let scale = match (&pic, self.mode) {
                (Some(p), Zoom::Fit) => self.fit_scale(p, [w, h]),
                (_, Zoom::Actual) => 1.0,
                _ => self.zoom,
            };
            if icon_button(ui, x, cy, "zoom-out", ui_a, false) {
                self.zoom_step(0.8);
            }
            x += 54.0;
            ui.text_raw(x, cy + 4.5, &format!("{:.0}%", scale * 100.0), 12.5, true, [1.0; 3], 0.9 * ui_a, Align::Center);
            x += 54.0;
            if icon_button(ui, x, cy, "zoom-in", ui_a, false) {
                self.zoom_step(1.25);
            }
            x += step;
            if icon_button(ui, x, cy, "maximize-2", ui_a, self.mode == Zoom::Fit) {
                self.mode = Zoom::Fit;
                self.pan = [0.0; 2];
            }
            x += step + 6.0;
            ui.fill([x - 3.0, cy - 11.0, 1.0, 22.0], 0.0, [1.0; 3], 0.15 * ui_a);
            x += 14.0;
            if icon_button(ui, x, cy, "rotate-cw", ui_a, false) {
                self.rotate(1);
            }
            x += step;
            if icon_button(ui, x, cy, "info", ui_a, self.info) {
                self.info = !self.info;
            }
            x += step;
            if icon_button(ui, x, cy, "monitor", ui_a, self.fullscreen) {
                self.fullscreen = !self.fullscreen;
                host.fullscreen = Some(self.fullscreen);
            }
            x += step;
            if icon_button(ui, x, cy, "trash-2", ui_a, false) {
                self.delete();
            }
        }

        // ---- the information panel
        if self.info {
            if let (Some(p), Some(pic)) = (&path, &pic) {
                let meta = std::fs::metadata(p).ok();
                let lines = [
                    ("Name", p.file_name().unwrap_or_default().to_string_lossy().to_string()),
                    ("Size", format!("{} × {} px", pic.w, pic.h)),
                    ("File", meta.as_ref().map(|m| human(m.len())).unwrap_or_default()),
                    ("Modified", meta.and_then(|m| m.modified().ok()).and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok()).map(|d| fsops::format_time(d.as_secs())).unwrap_or_default()),
                    ("Folder", p.parent().map(|d| d.display().to_string()).unwrap_or_default()),
                ];
                let pw = 330.0;
                ui.glass([w - pw - 16.0, 56.0, pw, 26.0 + lines.len() as f32 * 24.0], 14.0, 1.15);
                for (i, (k, v)) in lines.iter().enumerate() {
                    let y = 82.0 + i as f32 * 24.0;
                    ui.text(w - pw, y, k, 12.0, true, [1.0; 3], 0.5, Align::Left);
                    let v = fit_text(ui, v, 12.0, pw - 100.0);
                    ui.text_raw(w - pw + 72.0, y, &v, 12.0, false, [1.0; 3], 0.9, Align::Left);
                }
            }
        }

        // ---- the right-click menu
        if let Some(at) = self.ctx {
            let entries = [("copy", tr("Copy Picture").into_owned()), ("link", tr("Copy File Path").into_owned())];
            let (mw, rh) = (190.0, 32.0);
            let mh = entries.len() as f32 * rh + 12.0;
            let (mx, my) = (at[0].min(w - mw - 8.0).max(8.0), at[1].min(h - mh - 8.0).max(8.0));
            ui.glass([mx, my, mw, mh], 12.0, 1.3);
            let mut chosen = None;
            for (i, (icon, label)) in entries.iter().enumerate() {
                let r = [mx + 6.0, my + 6.0 + i as f32 * rh, mw - 12.0, rh];
                if ui.hit(r) {
                    ui.fill(r, 8.0, [1.0; 3], 0.16);
                    if ui.click {
                        chosen = Some(i);
                    }
                }
                ui.glyph(r[0] + 16.0, r[1] + rh / 2.0, 15.0, icon, [1.0; 3], 0.85);
                ui.text_raw(r[0] + 34.0, r[1] + rh / 2.0 + 4.5, label, 13.0, false, [1.0; 3], 0.95, Align::Left);
            }
            // any click closes it, on an entry or off it
            if ui.click {
                self.ctx = None;
                host.redraw = true;
            }
            match chosen {
                Some(0) => self.copy_picture(host),
                Some(1) => self.copy_path(host),
                _ => {}
            }
        }

        // window title follows the picture
        let title = path.as_ref().and_then(|p| p.file_name()).map(|n| format!("{} - {}", n.to_string_lossy(), tr("Pictures"))).unwrap_or_else(|| tr("Pictures").into_owned());
        if title != self.title {
            host.title = Some(title.clone());
            self.title = title;
        }
        // keep the neighbours coming and let the note go
        if !self.note.is_empty() && self.last_move.elapsed() > IDLE {
            self.note.clear();
        }
    }
}

impl Viewer {
    /// The picture on the screen as PNG on the clipboard.
    fn copy_picture(&mut self, host: &mut Host) {
        let Some(path) = self.current().cloned() else { return };
        // what is on the screen (turned, if it was), not the file as it lies on the disk
        let png = {
            let pic = self.cache.get(&path);
            pic.and_then(|pic| {
                let (px, w, h) = pic.pixels();
                // premultiplied BGRA to straight RGBA
                let mut rgba = Vec::with_capacity(px.len());
                for p in px.chunks_exact(4) {
                    let a = p[3] as u32;
                    let un = |c: u8| if a == 0 || a == 255 { c } else { ((c as u32 * 255 + a / 2) / a).min(255) as u8 };
                    rgba.extend_from_slice(&[un(p[2]), un(p[1]), un(p[0]), p[3]]);
                }
                let img = image::RgbaImage::from_raw(w as u32, h as u32, rgba)?;
                let mut out = Vec::new();
                let enc = image::codecs::png::PngEncoder::new_with_quality(std::io::Cursor::new(&mut out), image::codecs::png::CompressionType::Fast, image::codecs::png::FilterType::Adaptive);
                img.write_with_encoder(enc).ok()?;
                Some(out)
            })
        };
        match png {
            Some(png) => {
                host.copy_image = Some(png);
                self.note = tr("Picture copied").into_owned();
            }
            None => self.note = tr("Could not copy the picture").into_owned(),
        }
        host.redraw = true;
    }

    fn copy_path(&mut self, host: &mut Host) {
        if let Some(p) = self.current() {
            host.copy = Some(p.to_string_lossy().to_string());
            self.note = tr("Path copied").into_owned();
            host.redraw = true;
        }
    }

    fn zoom_step(&mut self, factor: f32) {
        let cur = if self.mode == Zoom::Custom { self.zoom } else { self.zoom.max(0.02) };
        self.zoom_at(factor, [0.0, 0.0], cur);
    }
}

fn fit_text(ui: &mut Ui<'_>, text: &str, size: f32, max: f32) -> String {
    if ui.measure_raw(text, size, false) <= max {
        return text.to_string();
    }
    let mut s = text.to_string();
    while !s.is_empty() && ui.measure_raw(&format!("…{s}"), size, false) > max {
        s.remove(0);
    }
    format!("…{s}")
}

fn main() {
    let arg = std::env::args().nth(1).map(PathBuf::from);
    app::run(Config::new("Memrium Pictures", "memrium-view").size(1100, 720).min_size(420, 320).decorations(Decorations::Client), Viewer::new(arg));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numbers_in_names_sort_as_numbers() {
        let mut v = vec!["img10.png", "IMG2.png", "img1.png", "img02b.png", "a.png"];
        v.sort_by(|a, b| natural(a, b));
        assert_eq!(v, ["a.png", "img1.png", "IMG2.png", "img02b.png", "img10.png"]);
    }

    #[test]
    fn only_pictures_are_listed_and_in_order() {
        let dir = std::env::temp_dir().join(format!("memrium_view_test_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        for n in ["b10.png", "b2.PNG", "note.txt", "c.jpg"] {
            std::fs::write(dir.join(n), b"x").unwrap();
        }
        let names: Vec<String> = pictures_in(&dir).iter().map(|p| p.file_name().unwrap().to_string_lossy().to_string()).collect();
        std::fs::remove_dir_all(&dir).ok();
        assert_eq!(names, ["b2.PNG", "b10.png", "c.jpg"]);
    }

    #[test]
    fn a_png_decodes_and_a_broken_file_says_so() {
        let dir = std::env::temp_dir().join(format!("memrium_view_dec_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let good = dir.join("ok.png");
        image::RgbaImage::from_pixel(5, 3, image::Rgba([10, 20, 30, 255])).save(&good).unwrap();
        let bad = dir.join("bad.png");
        std::fs::write(&bad, b"not a picture").unwrap();
        let pic = decode(&good).expect("a real png");
        assert_eq!((pic.w, pic.h), (5, 3));
        assert!(decode(&bad).is_err());
        std::fs::remove_dir_all(&dir).ok();
    }
}
