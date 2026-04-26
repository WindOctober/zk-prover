#![no_main]
sp1_zkvm::entrypoint!(main);

use zk_prover::{encode_c_source_to_cnf, CnfSummary};

pub fn main() {
    let source = sp1_zkvm::io::read::<String>();

    let encoded = encode_c_source_to_cnf(&source).expect("C-to-CNF frontend encoding failed");
    let summary = CnfSummary::from_encoded(&encoded);

    sp1_zkvm::io::commit(&summary);
}
