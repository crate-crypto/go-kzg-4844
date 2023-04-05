package gokzg4844

import (
	"github.com/crate-crypto/go-kzg-4844/internal/kzg"
)

// BlobToKZGCommitment implements [blob_to_kzg_commitment].
//
// [blob_to_kzg_commitment]: https://github.com/ethereum/consensus-specs/blob/3a2304981a3b820a22b518fe4859f4bba0ebc83b/specs/deneb/polynomial-commitments.md#blob_to_kzg_commitment
func (c *Context) BlobToKZGCommitment(blob Blob) (KZGCommitment, error) {
	// 1. Deserialization
	//
	// Deserialize blob into polynomial
	polynomial, err := DeserializeBlob(blob)
	if err != nil {
		return KZGCommitment{}, err
	}

	// 2. Commit to polynomial
	commitment, err := kzg.Commit(polynomial, c.commitKey)
	if err != nil {
		return KZGCommitment{}, err
	}

	// 3. Serialization
	//
	// Serialize commitment
	serComm := SerializeG1Point(*commitment)

	return KZGCommitment(serComm), nil
}

// ComputeBlobKZGProof implements [compute_blob_kzg_proof]. It takes a blob and returns the KZG proof that is used to
// verify it against the given KZG commitment at a random point.
//
// Note: This method does not check that the commitment corresponds to the `blob`. The method does still check that the
// commitment is a valid commitment. One should check this externally or call [Context.BlobToKZGCommitment].
//
// [compute_blob_kzg_proof]: https://github.com/ethereum/consensus-specs/blob/3a2304981a3b820a22b518fe4859f4bba0ebc83b/specs/deneb/polynomial-commitments.md#compute_blob_kzg_proof
func (c *Context) ComputeBlobKZGProof(blob Blob, blobCommitment KZGCommitment) (KZGProof, error) {
	// 1. Deserialization
	//
	polynomial, err := DeserializeBlob(blob)
	if err != nil {
		return KZGProof{}, err
	}

	// Deserialize commitment
	//
	// We only do this to check if it is in the correct subgroup
	_, err = DeserializeG1Point(G1Point(blobCommitment))
	if err != nil {
		return KZGProof{}, err
	}

	// 2. Compute Fiat-Shamir challenge
	evaluationChallenge := computeChallenge(blob, blobCommitment)

	// 3. Create opening proof
	openingProof, err := kzg.Open(c.domain, polynomial, evaluationChallenge, c.commitKey)
	if err != nil {
		return KZGProof{}, err
	}

	// 4. Serialization
	//
	// Quotient commitment
	kzgProof := SerializeG1Point(openingProof.QuotientCommitment)

	return KZGProof(kzgProof), nil
}

// ComputeKZGProof implements [compute_kzg_proof].
//
// [compute_kzg_proof]: https://github.com/ethereum/consensus-specs/blob/3a2304981a3b820a22b518fe4859f4bba0ebc83b/specs/deneb/polynomial-commitments.md#compute_kzg_proof
func (c *Context) ComputeKZGProof(blob Blob, inputPointBytes Scalar) (KZGProof, Scalar, error) {
	// 1. Deserialization
	//
	polynomial, err := DeserializeBlob(blob)
	if err != nil {
		return KZGProof{}, [32]byte{}, err
	}

	inputPoint, err := DeserializeScalar(inputPointBytes)
	if err != nil {
		return KZGProof{}, [32]byte{}, err
	}

	// 2. Create opening proof
	openingProof, err := kzg.Open(c.domain, polynomial, inputPoint, c.commitKey)
	if err != nil {
		return KZGProof{}, [32]byte{}, err
	}

	// 3. Serialization
	//
	kzgProof := SerializeG1Point(openingProof.QuotientCommitment)

	claimedValueBytes := SerializeScalar(openingProof.ClaimedValue)

	return KZGProof(kzgProof), claimedValueBytes, nil
}