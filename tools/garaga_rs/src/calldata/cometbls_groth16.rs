use lambdaworks_math::{field::traits::IsPrimeField, traits::ByteConversion};
use num_bigint::{BigInt, BigUint, Sign};

use crate::{
    algebra::{g1point::G1Point, polynomial::Polynomial},
    calldata::{
        full_proof_with_hints::groth16::{Groth16Proof, Groth16VerificationKey},
        mpc_calldata::mpc_calldata_builder,
        msm_calldata::msm_calldata_builder,
        G1PointBigUint, G2PointBigUint,
    },
    definitions::{
        BN254PrimeField, CurveID, CurveParamsProvider, FieldElement, Stark252PrimeField,
    },
    io::{
        biguint_split, element_from_biguint, element_to_biguint, field_elements_from_big_uints,
        parse_g1_points_from_flattened_field_elements_list,
    },
};

pub struct MPCheckHintBN254 {
    pub lambda_root: Polynomial<BN254PrimeField>,
    pub lambda_root_inverse: Polynomial<BN254PrimeField>,
    pub w: FieldElement<BN254PrimeField>,
    pub ris: Vec<Polynomial<BN254PrimeField>>,
    pub big_q: Vec<FieldElement<BN254PrimeField>>,
    pub z: FieldElement<Stark252PrimeField>,
}

pub struct CometblsGroth16Proof {
    pub groth16_proof: Groth16Proof,
    pub proof_commitment: G1PointBigUint,
    pub proof_commitment_pok: G1PointBigUint,
    pub mpcheck_hint: MPCheckHintBN254,
    pub commitment_mpcheck_hint: MPCheckHintBN254,
    pub msm_hint: Vec<FieldElement<Stark252PrimeField>>,
}

pub struct CometblsGroth16VerifyingKey {
    pub groth16_vk: Groth16VerificationKey,
    pub commitment_key_g: G2PointBigUint,
    pub commitment_key_g_root_sigma_neg: G2PointBigUint,
}

impl CometblsGroth16Proof {
    pub fn generate_calldata(
        proof: Groth16Proof,
        vk: CometblsGroth16VerifyingKey,
        proof_commitment: G1PointBigUint,
        proof_commitment_pok: G1PointBigUint,
    ) -> Vec<BigUint> {
        let mut calldata: Vec<BigUint> = Vec::new();
        // Calculate vk_x
        let vk_x = vk_x_handle_curve::<BN254PrimeField>(
            &vk.groth16_vk,
            &proof.public_inputs,
            &proof_commitment,
        );

        // MPC calldata
        let mut mpc_values: Vec<BigUint> = vec![];
        mpc_values.extend(vk_x.flatten());
        mpc_values.extend(vk.groth16_vk.gamma.flatten());
        mpc_values.extend(proof.c.flatten());
        mpc_values.extend(vk.groth16_vk.delta.flatten());
        mpc_values.extend(proof.a.neg(CurveID::BN254).flatten());
        mpc_values.extend(proof.b.flatten());

        let mut mpc_public_pair: Vec<BigUint> = vec![];
        mpc_public_pair.extend(vk.groth16_vk.alpha.flatten());
        mpc_public_pair.extend(vk.groth16_vk.beta.flatten());

        let mpc_calldata =
            mpc_calldata_builder(CurveID::BN254 as usize, &mpc_values, 2, &mpc_public_pair)
                .unwrap();

        let mut mpc_values: Vec<BigUint> = vec![];
        mpc_values.extend(proof_commitment.flatten());
        mpc_values.extend(vk.commitment_key_g.flatten());
        mpc_values.extend(proof_commitment_pok.flatten());
        mpc_values.extend(vk.commitment_key_g_root_sigma_neg.flatten());

        let commitment_mpc_calldata =
            mpc_calldata_builder(CurveID::BN254 as usize, &mpc_values, 2, &[]).unwrap();

        let msm_calldata = msm_calldata_builder(
            &vk.groth16_vk
                .ic
                .iter()
                .skip(1)
                .flat_map(|point| vec![point.x.clone(), point.y.clone()])
                .collect::<Vec<BigUint>>(),
            &proof.public_inputs,
            CurveID::BN254 as usize,
            false,
            true,
        )
        .unwrap();

        calldata.extend(proof.serialize_to_calldata());
        calldata.extend(
            biguint_split::<4, 96>(&proof_commitment.x)
                .into_iter()
                .map(Into::into)
                .collect::<Vec<BigUint>>(),
        );
        calldata.extend(
            biguint_split::<4, 96>(&proof_commitment.y)
                .into_iter()
                .map(Into::into)
                .collect::<Vec<BigUint>>(),
        );
        calldata.extend(
            biguint_split::<4, 96>(&proof_commitment_pok.x)
                .into_iter()
                .map(Into::into)
                .collect::<Vec<BigUint>>(),
        );
        calldata.extend(
            biguint_split::<4, 96>(&proof_commitment_pok.y)
                .into_iter()
                .map(Into::into)
                .collect::<Vec<BigUint>>(),
        );
        calldata.extend(mpc_calldata);
        calldata.extend(commitment_mpc_calldata);
        calldata.extend(msm_calldata);

        calldata
    }
}

fn vk_x_handle_curve<F>(
    vk: &Groth16VerificationKey,
    pub_inputs: &[BigUint],
    commitment: &G1PointBigUint,
) -> G1PointBigUint
where
    F: IsPrimeField + CurveParamsProvider<F>,
    FieldElement<F>: ByteConversion,
{
    // Parse IC points from BigUint to FieldElement
    let ic_elements = field_elements_from_big_uints::<F>(
        &vk.ic
            .iter()
            .flat_map(|point| vec![point.x.clone(), point.y.clone()])
            .collect::<Vec<BigUint>>(),
    );
    let ic_points = parse_g1_points_from_flattened_field_elements_list(&ic_elements).unwrap();

    let commitment = G1Point::new(
        element_from_biguint(&commitment.x),
        element_from_biguint(&commitment.y),
        false,
    )
    .unwrap();

    // Start with IC[0]
    let mut vk_x = ic_points[0].clone().add(&commitment);

    // Compute IC[0] + pub_input_i * IC[i] for each public input
    for (i, pub_input) in pub_inputs.iter().enumerate() {
        let pub_input_bigint = BigInt::from_biguint(Sign::Plus, pub_input.clone());
        let scaled_ic = ic_points[i + 1].scalar_mul(pub_input_bigint);
        vk_x = vk_x.add(&scaled_ic);
    }

    // Convert G1Point back to G1PointBigUint
    G1PointBigUint {
        x: element_to_biguint(&vk_x.x),
        y: element_to_biguint(&vk_x.y),
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use serde_json::Value;

    use super::*;
    #[test]
    fn test_generate_calldata() {
        let proof: Value = serde_json::from_str(include_str!(
            "/home/aeryz/dev/union/union/gnark_proof_bn254.json"
        ))
        .unwrap();

        let public_inputs: Value = serde_json::from_str(include_str!(
            "/home/aeryz/dev/union/union/gnark_public_bn254.json"
        ))
        .unwrap();

        let vk: Value = serde_json::from_str(include_str!(
            "/home/aeryz/dev/union/union/gnark_vk_bn254.json"
        ))
        .unwrap();

        let parse_bigint = |val: Value| {
            let x: String = serde_json::from_value(val).unwrap();
            let bigint = BigUint::from_str(&x).unwrap();
            bigint
        };

        let p = Groth16Proof {
            a: G1PointBigUint {
                x: parse_bigint(proof["Ar"]["X"].clone()),
                y: parse_bigint(proof["Ar"]["Y"].clone()),
            },
            b: G2PointBigUint {
                x0: parse_bigint(proof["Bs"]["X"]["A0"].clone()),
                x1: parse_bigint(proof["Bs"]["X"]["A1"].clone()),
                y0: parse_bigint(proof["Bs"]["Y"]["A0"].clone()),
                y1: parse_bigint(proof["Bs"]["Y"]["A1"].clone()),
            },
            c: G1PointBigUint {
                x: parse_bigint(proof["Krs"]["X"].clone()),
                y: parse_bigint(proof["Krs"]["Y"].clone()),
            },
            public_inputs: vec![
                parse_bigint(public_inputs["X"].clone()),
                parse_bigint(public_inputs["Y"].clone()),
            ],
            image_id_journal_risc0: None,
            vkey_public_values_sp1: None,
        };

        let vk = CometblsGroth16VerifyingKey {
            groth16_vk: Groth16VerificationKey {
                alpha: G1PointBigUint {
                    x: parse_bigint(vk["G1"]["Alpha"]["X"].clone()),
                    y: parse_bigint(vk["G1"]["Alpha"]["Y"].clone()),
                },
                beta: G2PointBigUint {
                    x0: parse_bigint(vk["G2"]["Beta"]["X"]["A0"].clone()),
                    x1: parse_bigint(vk["G2"]["Beta"]["X"]["A1"].clone()),
                    y0: parse_bigint(vk["G2"]["Beta"]["Y"]["A0"].clone()),
                    y1: parse_bigint(vk["G2"]["Beta"]["Y"]["A1"].clone()),
                },
                delta: G2PointBigUint {
                    x0: parse_bigint(vk["G2"]["Delta"]["X"]["A0"].clone()),
                    x1: parse_bigint(vk["G2"]["Delta"]["X"]["A1"].clone()),
                    y0: parse_bigint(vk["G2"]["Delta"]["Y"]["A0"].clone()),
                    y1: parse_bigint(vk["G2"]["Delta"]["Y"]["A1"].clone()),
                },
                gamma: G2PointBigUint {
                    x0: parse_bigint(vk["G2"]["Gamma"]["X"]["A0"].clone()),
                    x1: parse_bigint(vk["G2"]["Gamma"]["X"]["A1"].clone()),
                    y0: parse_bigint(vk["G2"]["Gamma"]["Y"]["A0"].clone()),
                    y1: parse_bigint(vk["G2"]["Gamma"]["Y"]["A1"].clone()),
                },
                ic: vec![
                    G1PointBigUint {
                        x: parse_bigint(vk["G1"]["K"][0]["X"].clone()),
                        y: parse_bigint(vk["G1"]["K"][0]["Y"].clone()),
                    },
                    G1PointBigUint {
                        x: parse_bigint(vk["G1"]["K"][1]["X"].clone()),
                        y: parse_bigint(vk["G1"]["K"][1]["Y"].clone()),
                    },
                    G1PointBigUint {
                        x: parse_bigint(vk["G1"]["K"][2]["X"].clone()),
                        y: parse_bigint(vk["G1"]["K"][2]["Y"].clone()),
                    },
                ],
            },
            commitment_key_g: G2PointBigUint {
                x0: parse_bigint(vk["CommitmentKey"]["G"]["X"]["A0"].clone()),
                x1: parse_bigint(vk["CommitmentKey"]["G"]["X"]["A1"].clone()),
                y0: parse_bigint(vk["CommitmentKey"]["G"]["Y"]["A0"].clone()),
                y1: parse_bigint(vk["CommitmentKey"]["G"]["Y"]["A1"].clone()),
            },
            commitment_key_g_root_sigma_neg: G2PointBigUint {
                x0: parse_bigint(vk["CommitmentKey"]["GRootSigmaNeg"]["X"]["A0"].clone()),
                x1: parse_bigint(vk["CommitmentKey"]["GRootSigmaNeg"]["X"]["A1"].clone()),
                y0: parse_bigint(vk["CommitmentKey"]["GRootSigmaNeg"]["Y"]["A0"].clone()),
                y1: parse_bigint(vk["CommitmentKey"]["GRootSigmaNeg"]["Y"]["A1"].clone()),
            },
        };

        let proof_commitment = G1PointBigUint {
            x: parse_bigint(proof["Commitments"][0]["X"].clone()),
            y: parse_bigint(proof["Commitments"][0]["Y"].clone()),
        };

        let proof_commitment_pok = G1PointBigUint {
            x: parse_bigint(proof["CommitmentPok"]["X"].clone()),
            y: parse_bigint(proof["CommitmentPok"]["Y"].clone()),
        };

        let calldata =
            CometblsGroth16Proof::generate_calldata(p, vk, proof_commitment, proof_commitment_pok);

        for i in calldata {
            println!("0x{i:x}");
        }
    }
}
