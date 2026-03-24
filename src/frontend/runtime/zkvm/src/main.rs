#![no_main]
sp1_zkvm::entrypoint!(main);

use zk_prover::{validate_translation_artifact, TranslationArtifact};

pub fn main() {
    let artifact = sp1_zkvm::io::read::<TranslationArtifact>();

    println!("cycle-tracker-report-start: validate");
    let summary = validate_translation_artifact(&artifact)
        .expect("verification-layer SAT artifact validation failed");
    println!("cycle-tracker-report-end: validate");

    sp1_zkvm::io::commit(&summary);
}
