# Canonical `BLINCS-48-X` Test Vectors

Canonical byte-for-byte test vectors for the **`BLINCS-48-X`** suite (`SPEC.md`, draft `0.5.0`, `3,990` bytes, `q = 2^48`). Every vector below is independently cross-verified by both [`reference/`](../reference) (Rust) and pure-Python BLAKE3.

## Seed and SignetId

- `seed` (`32 B`): `000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f`
- `SignetId` (`32 B`): `7ee7fe20dac820b17625cad3a38a8af696a69a74992f01a7c9ed3680699d2c5c`

## `reference-imprint-1.bin` (`3,990` bytes)

- `draw` (`32 B`): `[0x07; 32]`
- `ctx`: `b"BLINCS-48-X reference vector v1"` (`31` bytes)
- `msg`: `b"hello, BLINCS"` (`13` bytes)
- `SHA-256`: `5ddc2156d48938300f73abfa21fe514b69ed56ffbb44c61b2dc2d2bb6a4f9386`
- `BLAKE3`: `cefb8846c95ff890a8e7cb1a51a2d2c2032c3f0de9e57fef8fc3d7943723ac22`
- Intermediate KATs:
  - `e`: `9a70dfb49286d13de2a56ed4374946eb`
  - `K_msg`: `28b5bf0bad61349ba7f2cc3ba730cd3b1fd1a8a58fff9acc8115f154fe044847`
  - `h_msg`: `7d978bc5d7a7df9bd2ff34dd4288dbf51963eb8da05365a9cc53ea2d05e2e09a`
  - `R`: `32b08c4c9d15504265fa2984b9b7cf25`
  - `D_seed`: `2151d28e0fd8b76f3d514feb22bc966bb26fab87dee126eb3917d320072f30f9`
  - `ctr_ft = 5530`, `sibs = 45/45`, `leaf_addr = 0xbbce641c7560` (`bit 47 = 1`), `layer_ctrs = [595, 4088, 413, 3803, 1277, 1312]`.

## `edge-vectors.json` (`33,883` bytes)

- `SHA-256`: `89437ccbd170293b5ec20e621a7d528e12696837e681097bff2d24434f3e6a9e`
- `BLAKE3`: `524d43dea3d631e2baabc04e98f70c7362c6a1ac630d5331f9bd2eee44a88704`
- Four boundary vectors:
  1. `empty` (`0 B` msg, `0 B` ctx, `sibs = 43/45` — 2 zero-padded Octopus slots)
  2. `one-byte-zero` (`1 B` `0x00` msg, `sibs = 44/45` — 1 zero-padded Octopus slot)
  3. `chunk-1024` (`1,024 B` BLAKE3 chunk boundary, `255 B` max context, `bit 47 = 1`)
  4. `stream-16385-high-leaf` (`16,385 B` multi-chunk streaming boundary, `bit 47 = 1`)
