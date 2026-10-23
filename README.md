# memrium-view

An image viewer with gliding zoom and neighbour preloading.

Part of [Memrium](https://github.com/Supchik22/memrium-desktop), a configurable Wayland desktop. The program is built on
[Chebrium](https://github.com/Supchik22/chebrium), the desktop's UI toolkit, and runs as a standalone Wayland client.
It follows the look of the shell when one is running and has a sensible look of its own otherwise.

## Build and run

```
cargo run --release
```

The first build is slow: the dependencies (Chebrium and the Memrium shell library) are fetched from GitHub. To build the
whole desktop at once, use [memrium-desktop](https://github.com/Supchik22/memrium-desktop).

License: MIT.
