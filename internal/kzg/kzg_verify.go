package kzg

import (
	"math/big"

	"github.com/consensys/gnark-crypto/ecc"
	bls12381 "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/crate-crypto/go-kzg-4844/internal/utils"
)

// OpeningProof is a struct holding a (cryptographic) proof to the claim that a polynomial f(X) (represented by a
// commitment to it) evaluates at a point `z` to `f(z)`.
type OpeningProof struct {
	// Commitment to quotient polynomial (f(X) - f(z))/(X-z)
	QuotientCommitment bls12381.G1Affine

	// Point that we are evaluating the polynomial at : `z`
	InputPoint fr.Element

	// ClaimedValue purported value : `f(z)`
	ClaimedValue fr.Element
}

// Verify a single KZG proof. See [verify_kzg_proof_impl]. Returns `nil` if verification was successful, an error
// otherwise. If verification failed due to the pairings check it will return [ErrVerifyOpeningProof].
//
// Note: We could make this method faster by storing pre-computations for the generators in G1 and G2
// as we only do scalar multiplications with those in this method.
//
// Modified from [gnark-crypto].
//
// [verify_kzg_proof_impl]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#verify_kzg_proof_impl
// [gnark-crypto]: https://github.com/ConsenSys/gnark-crypto/blob/8f7ca09273c24ed9465043566906cbecf5dcee91/ecc/bls12-381/fr/kzg/kzg.go#L166
func Verify(commitment *Commitment, proof *OpeningProof, openKey *OpeningKey) error {

	// [f(α)]G₁ + [-α]([H(z)]G₁) = [f(α) - α*H(z)]G₁
	var totalG1 bls12381.G1Jac
	var pointNeg fr.Element
	var cmInt, pointInt big.Int
	proof.ClaimedValue.BigInt(&cmInt)
	pointNeg.Neg(&proof.InputPoint).BigInt(&pointInt)
	totalG1.JointScalarMultiplication(&openKey.GenG1, &proof.QuotientCommitment, &cmInt, &pointInt)

	// [f(α) - α*H(z)]G₁ + [-f(z)]G₁  = [f(α) - f(z) - α*H(z)]G₁
	var commitmentJac bls12381.G1Jac
	commitmentJac.FromAffine(commitment)
	totalG1.SubAssign(&commitmentJac)

	// e([f(z)-f(α)+aH(z)]G₁], G₂).e([-H(z)]G₁, [z]G₂) == 1
	var totalG1Aff bls12381.G1Affine
	totalG1Aff.FromJacobian(&totalG1)
	check, err := bls12381.PairingCheckFixedQ(
		[]bls12381.G1Affine{totalG1Aff, proof.QuotientCommitment},
		openKey.PairingLines[:],
	)

	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}

	return nil
}

// BatchVerifyMultiPoints verifies multiple KZG proofs in a batch. See [verify_kzg_proof_batch].
//
//   - This method is more efficient than calling [Verify] multiple times.
//   - Randomness is used to combine multiple proofs into one.
//
// Modified from [gnark-crypto].
//
// [verify_kzg_proof_batch]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#verify_kzg_proof_batch
// [gnark-crypto]: https://github.com/ConsenSys/gnark-crypto/blob/8f7ca09273c24ed9465043566906cbecf5dcee91/ecc/bls12-381/fr/kzg/kzg.go#L367)
func BatchVerifyMultiPoints(commitments []Commitment, proofs []OpeningProof, openKey *OpeningKey) error {
	// Check consistency number of proofs is equal to the number of commitments.
	if len(commitments) != len(proofs) {
		return ErrInvalidNumDigests
	}
	batchSize := len(commitments)

	// If there is nothing to verify, we return nil
	// to signal that verification was true.
	//
	if batchSize == 0 {
		return nil
	}

	// If batch size is `1`, call Verify
	if batchSize == 1 {
		return Verify(&commitments[0], &proofs[0], openKey)
	}

	// Sample random numbers for sampling.
	//
	// We only need to sample one random number and
	// compute powers of that random number. This works
	// since powers will produce a vandermonde matrix
	// which is linearly independent.
	var randomNumber fr.Element
	_, err := randomNumber.SetRandom()
	if err != nil {
		return err
	}
	randomNumbers := utils.ComputePowers(randomNumber, uint(batchSize))

	// Combine random_i*quotient_i
	var foldedQuotients bls12381.G1Affine
	quotients := make([]bls12381.G1Affine, len(proofs))
	for i := 0; i < batchSize; i++ {
		quotients[i].Set(&proofs[i].QuotientCommitment)
	}
	config := ecc.MultiExpConfig{}
	_, err = foldedQuotients.MultiExp(quotients, randomNumbers, config)
	if err != nil {
		return err
	}

	// Fold commitments and evaluations using randomness
	evaluations := make([]fr.Element, batchSize)
	for i := 0; i < len(randomNumbers); i++ {
		evaluations[i].Set(&proofs[i].ClaimedValue)
	}
	foldedCommitments, foldedEvaluations, err := fold(commitments, evaluations, randomNumbers)
	if err != nil {
		return err
	}

	// Compute commitment to folded Eval
	var foldedEvaluationsCommit bls12381.G1Affine
	var foldedEvaluationsBigInt big.Int
	foldedEvaluations.BigInt(&foldedEvaluationsBigInt)
	foldedEvaluationsCommit.ScalarMultiplication(&openKey.GenG1, &foldedEvaluationsBigInt)

	// Compute F = foldedCommitments - foldedEvaluationsCommit
	foldedCommitments.Sub(&foldedCommitments, &foldedEvaluationsCommit)

	// Combine random_i*(point_i*quotient_i)
	var foldedPointsQuotients bls12381.G1Affine
	for i := 0; i < batchSize; i++ {
		randomNumbers[i].Mul(&randomNumbers[i], &proofs[i].InputPoint)
	}
	_, err = foldedPointsQuotients.MultiExp(quotients, randomNumbers, config)
	if err != nil {
		return err
	}

	// `lhs` first pairing
	foldedCommitments.Add(&foldedCommitments, &foldedPointsQuotients)

	// `lhs` second pairing
	foldedQuotients.Neg(&foldedQuotients)

	check, err := bls12381.PairingCheck(
		[]bls12381.G1Affine{foldedCommitments, foldedQuotients},
		[]bls12381.G2Affine{openKey.GenG2, openKey.AlphaG2},
	)
	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}

	return nil
}

// fold computes two inner products with the same factors:
//
//   - Between commitments and factors; This is a multi-exponentiation.
//   - Between evaluations and factors; This is a dot product.
//
// Modified slightly from [gnark-crypto].
//
// [gnark-crypto]: https://github.com/ConsenSys/gnark-crypto/blob/8f7ca09273c24ed9465043566906cbecf5dcee91/ecc/bls12-381/fr/kzg/kzg.go#L464
func fold(commitments []Commitment, evaluations, factors []fr.Element) (Commitment, fr.Element, error) {
	// Length inconsistency between commitments and evaluations should have been done before calling this function
	batchSize := len(commitments)

	// Fold the claimed values
	var foldedEvaluations, tmp fr.Element
	for i := 0; i < batchSize; i++ {
		tmp.Mul(&evaluations[i], &factors[i])
		foldedEvaluations.Add(&foldedEvaluations, &tmp)
	}

	// Fold the commitments
	var foldedCommitments Commitment
	_, err := foldedCommitments.MultiExp(commitments, factors, ecc.MultiExpConfig{})
	if err != nil {
		return foldedCommitments, foldedEvaluations, err
	}

	return foldedCommitments, foldedEvaluations, nil
}
