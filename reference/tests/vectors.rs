//! Exhaustive canonical test-vector verification for `blincs-reference` (`BLINCS-48-X`).

use blake3_servil_core::convenience::hash;
use blincs_reference::{
    IMPRINT_LEN, Signet, SignetId, UPORS_C, UPORS_LEN, UPORS_STEPS, UPORS_SUM, WOTS_N, WOTS_STEPS,
    WOTS_SUM, WOTS_Z, decode_wots_c, hex_unrank, self_test,
};

fn decode_hex(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2));
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn startup_self_test_passes() {
    self_test();
}

#[test]
fn hex_unrank_invariants_hold() {
    let mut prev: Option<[usize; 3]> = None;
    let mut all = Vec::with_capacity(UPORS_C);
    for i in 0..UPORS_C {
        let cw = hex_unrank(i);
        assert_eq!(cw[0] + cw[1] + cw[2], UPORS_SUM);
        assert!(cw.iter().all(|&x| x <= UPORS_STEPS));
        if let Some(p) = prev {
            assert!(p < cw, "hex_unrank not strictly lexicographic at {i}");
        }
        prev = Some(cw);
        all.push(cw);
    }
    for (i, a) in all.iter().enumerate() {
        for (j, b) in all.iter().enumerate() {
            if i != j {
                assert!(
                    !(a[0] <= b[0] && a[1] <= b[1] && a[2] <= b[2]),
                    "antichain violated at ({i}, {j})"
                );
            }
        }
    }
}

#[test]
fn wots_c_decode_bounds_and_antichain_hold() {
    let pack = |z: u128, ds: [usize; WOTS_N]| -> [u8; 32] {
        let mut lo = z & 3;
        for (i, &d) in ds.iter().enumerate() {
            lo |= u128::try_from(d).unwrap() << (WOTS_Z + 6 * i);
        }
        let mut out = [0u8; 32];
        out[..16].copy_from_slice(&lo.to_le_bytes());
        out
    };
    // Valid vector summing to 679 (11 * 32 + 9 * 33 + 1 * 30 = 352 + 297 + 30 = 679)
    let mut v1 = [32usize; WOTS_N];
    for x in &mut v1[11..20] {
        *x = 33;
    }
    v1[20] = 30;
    assert_eq!(v1.iter().sum::<usize>(), WOTS_SUM);
    let d1 = pack(0, v1);
    assert_eq!(decode_wots_c(&d1), Some(v1));

    // Non-zero z bits must reject.
    for z in 1u128..=3 {
        assert_eq!(decode_wots_c(&pack(z, v1)), None);
    }
    // Wrong sum must reject.
    let mut v_bad_sum = v1;
    v_bad_sum[0] += 1;
    assert_eq!(decode_wots_c(&pack(0, v_bad_sum)), None);
    // Out-of-range 6-bit digit (>= 60) must reject even if sum == 679.
    let mut v_bad_digit = v1;
    v_bad_digit[0] = 60;
    v_bad_digit[1] -= 28;
    assert_eq!(v_bad_digit.iter().sum::<usize>(), WOTS_SUM);
    assert_eq!(decode_wots_c(&pack(0, v_bad_digit)), None);

    // Distinct valid vectors form a strict antichain.
    let mut v2 = v1;
    v2[0] += 1;
    v2[1] -= 1;
    assert!(v2.iter().all(|&x| x <= WOTS_STEPS));
    let dec1 = decode_wots_c(&pack(0, v1)).unwrap();
    let dec2 = decode_wots_c(&pack(0, v2)).unwrap();
    assert!(!dec1.iter().zip(dec2.iter()).all(|(a, b)| a <= b));
    assert!(!dec2.iter().zip(dec1.iter()).all(|(a, b)| a <= b));
}

#[test]
fn matches_canonical_reference_vector_byte_for_byte() {
    let seed: [u8; 32] = core::array::from_fn(|i| u8::try_from(i).unwrap());
    let draw = [0x07u8; 32];
    let ctx = b"BLINCS-48-X reference vector v1";
    let msg = b"hello, BLINCS";

    let signet = Signet::from_seed(&seed);
    let expected_id: [u8; 32] =
        decode_hex("7ee7fe20dac820b17625cad3a38a8af696a69a74992f01a7c9ed3680699d2c5c")
            .try_into()
            .unwrap();
    assert_eq!(signet.id(), SignetId(expected_id));

    let imp = signet.imprint_deterministic(&draw, ctx, msg);
    let expected = include_bytes!("../../test_vectors/reference-imprint-1.bin");
    assert_eq!(&imp, expected);
    assert_eq!(
        hash(&imp).as_bytes(),
        decode_hex("cefb8846c95ff890a8e7cb1a51a2d2c2032c3f0de9e57fef8fc3d7943723ac22").as_slice()
    );

    assert!(signet.id().verify(ctx, msg, &imp));
    assert!(!signet.id().verify(ctx, b"hello, BLINCs", &imp));
    assert!(!signet.id().verify(b"wrong context", msg, &imp));
    assert!(!signet.id().verify(&[0u8; 256], msg, &imp));

    // Bit-flip checks across salt, randomizer, U-PORS, and every hypertree layer.
    for offset in [
        0,
        16,
        32,
        36,
        468,
        1187,
        1188,
        1191,
        1639,
        2090,
        2541,
        2992,
        3443,
        IMPRINT_LEN - 1,
    ] {
        let mut bad = imp;
        bad[offset] ^= 0x80;
        assert!(
            !signet.id().verify(ctx, msg, &bad),
            "accepted bit flip at byte {offset}"
        );
    }
}

#[test]
fn matches_all_four_edge_vectors_byte_for_byte() {
    let raw = include_str!("../../test_vectors/edge-vectors.json");
    let seed: [u8; 32] = core::array::from_fn(|i| u8::try_from(i).unwrap());
    let signet = Signet::from_seed(&seed);

    let messages: [(&str, Vec<u8>); 4] = [
        ("empty", vec![]),
        ("one-byte-zero", vec![0u8]),
        (
            "chunk-1024",
            (0..1024usize)
                .map(|i| u8::try_from((i * 31) & 0xff).unwrap())
                .collect(),
        ),
        (
            "stream-16385-high-leaf",
            (0..16385usize)
                .map(|i| u8::try_from((i * 37 + 5) & 0xff).unwrap())
                .collect(),
        ),
    ];

    let blocks: Vec<&str> = raw.split("\"name\": \"").skip(1).collect();
    assert_eq!(blocks.len(), messages.len());
    for (block, (expected_name, msg)) in blocks.iter().zip(messages.iter()) {
        let field = |key: &str| -> String {
            let needle = format!("\"{key}\": \"");
            let start = block.find(&needle).unwrap() + needle.len();
            let end = block[start..].find('"').unwrap() + start;
            block[start..end].to_owned()
        };

        let name_end = block.find('"').unwrap();
        assert_eq!(&block[..name_end], *expected_name);
        let draw: [u8; 32] = decode_hex(&field("draw_hex")).try_into().unwrap();
        let ctx = decode_hex(&field("ctx_hex"));
        let expected_imp: [u8; IMPRINT_LEN] = decode_hex(&field("imprint_hex")).try_into().unwrap();
        let expected_b3 = decode_hex(&field("imprint_blake3"));

        let got = signet.imprint_deterministic(&draw, &ctx, msg);
        assert_eq!(
            got, expected_imp,
            "edge vector {expected_name} imprint bytes mismatch"
        );
        assert_eq!(
            hash(&got).as_bytes(),
            expected_b3.as_slice(),
            "edge vector {expected_name} BLAKE3 mismatch"
        );
        assert!(
            signet.id().verify(&ctx, msg, &got),
            "edge vector {expected_name} failed verify"
        );

        // Verify canonical trailing zero-padding check on `one-byte-zero` (sibs = 44 / 45).
        if *expected_name == "one-byte-zero" {
            let last_pad_byte = 32 + UPORS_LEN - 1;
            assert_eq!(got[last_pad_byte], 0);
            let mut bad_pad = got;
            bad_pad[last_pad_byte] = 1;
            assert!(
                !signet.id().verify(&ctx, msg, &bad_pad),
                "accepted non-zero Octopus trailing padding"
            );
        }
    }
}
