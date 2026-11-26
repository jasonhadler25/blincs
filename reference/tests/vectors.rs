//! Exhaustive canonical test-vector verification for `blincs-reference`.

use blake3_servil_core::convenience::hash;
use blincs_reference::{
    IMPRINT_LEN, Signet, SignetId, UFORS_CODE, UFORS_STEPS, UFORS_SUM, self_test, wots_digits,
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
fn ufors_code_invariants_hold() {
    assert_eq!(UFORS_CODE.len(), 64);
    for (i, &cw) in UFORS_CODE.iter().enumerate() {
        let sum: usize = cw.iter().map(|&x| usize::from(x)).sum();
        assert_eq!(sum, UFORS_SUM, "codeword {i} sum mismatch");
        assert!(
            cw.iter().all(|&x| usize::from(x) <= UFORS_STEPS),
            "codeword {i} out of range"
        );
        if i > 0 {
            assert!(
                UFORS_CODE[i - 1] < cw,
                "UFORS_CODE not strictly lexicographically sorted at {i}"
            );
        }
        for (j, &other) in UFORS_CODE.iter().enumerate() {
            if i != j {
                assert!(
                    !(cw[0] <= other[0] && cw[1] <= other[1] && cw[2] <= other[2]),
                    "antichain violated at ({i}, {j})"
                );
            }
        }
    }
}

#[test]
fn matches_canonical_reference_vector_byte_for_byte() {
    let seed: [u8; 32] = core::array::from_fn(|i| u8::try_from(i).unwrap());
    let draw = [0x07u8; 32];
    let ctx = b"BLINCS-128-7x5 reference vector v1";
    let msg = b"hello, BLINCS";

    let signet = Signet::from_seed(&seed);
    let expected_id: [u8; 32] =
        decode_hex("98a5b8314b854e78f72cbadc9f5ed67c15bc2ad253cd98be1d5951595f217512")
            .try_into()
            .unwrap();
    assert_eq!(signet.id(), SignetId(expected_id));

    let imp = signet.imprint_deterministic(&draw, ctx, msg);
    let expected = include_bytes!("../../test_vectors/reference-imprint-1.bin");
    assert_eq!(&imp, expected);
    assert_eq!(
        hash(&imp).as_bytes(),
        decode_hex("e9e433283ad714c487275b7dcc747fb5e93c7f43d98353d24dd98d2e4794b231").as_slice()
    );

    assert!(signet.id().verify(ctx, msg, &imp));
    assert!(!signet.id().verify(ctx, b"hello, BLINCs", &imp));
    assert!(!signet.id().verify(b"wrong context", msg, &imp));
    assert!(!signet.id().verify(&[0u8; 256], msg, &imp));

    // Bit-flip checks across salt, randomizer, U-FORS, and every hypertree layer.
    for offset in [
        0,
        16,
        32,
        1951,
        1952,
        2592,
        3232,
        3872,
        4512,
        5152,
        5792,
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
    }
}

#[test]
fn wots_digits_checksum_dominance_sanity() {
    let a = [0x00u8; 16];
    let b = [0xffu8; 16];
    let da = wots_digits(&a);
    let db = wots_digits(&b);
    assert!(da[0..32].iter().all(|&x| x == 0));
    assert_eq!((da[32], da[33], da[34]), (0, 14, 1)); // 480 = 0x1e0
    assert!(db[0..32].iter().all(|&x| x == 15));
    assert_eq!((db[32], db[33], db[34]), (0, 0, 0)); // 0
}
