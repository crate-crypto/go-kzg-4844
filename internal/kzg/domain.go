package kzg

import (
	"errors"
	"fmt"
	"math/big"
	"math/bits"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/crate-crypto/go-proto-danksharding-crypto/internal/utils"
)

type Domain struct {
	Cardinality    uint64
	CardinalityInv fr.Element
	// Generator for the multiplicative subgroup
	// Not the primitive generator for the field
	Generator    fr.Element
	GeneratorInv fr.Element

	// Roots of unity for the multiplicative subgroup
	Roots []fr.Element

	// Precomputed inverses of the domain which
	// we will use to speed up the computation
	// f(x)/g(x) where g(x) is a linear polynomial
	// which vanishes on a point on the domain
	PreComputedInverses []fr.Element
}

// Copied and modified from fft.NewDomain
func NewDomain(m uint64) *Domain {
	domain := &Domain{}
	x := ecc.NextPowerOfTwo(m)
	domain.Cardinality = uint64(x)

	// generator of the largest 2-adic subgroup
	var rootOfUnity fr.Element

	rootOfUnity.SetString("10238227357739495823651030575849232062558860180284477541189508159991286009131")
	const maxOrderRoot uint64 = 32

	// find generator for Z/2^(log(m))Z
	logx := uint64(bits.TrailingZeros64(x))
	if logx > maxOrderRoot {
		panic(fmt.Sprintf("m (%d) is too big: the required root of unity does not exist", m))
	}

	// Generator = FinerGenerator^2 has order x
	expo := uint64(1 << (maxOrderRoot - logx))
	domain.Generator.Exp(rootOfUnity, big.NewInt(int64(expo))) // order x
	domain.GeneratorInv.Inverse(&domain.Generator)
	domain.CardinalityInv.SetUint64(uint64(x)).Inverse(&domain.CardinalityInv)

	// Compute the roots of unity for the multiplicative subgroup
	domain.Roots = make([]fr.Element, x)
	current := fr.One()
	for i := uint64(0); i < x; i++ {
		domain.Roots[i] = current
		current.Mul(&current, &domain.Generator)
	}

	// Compute precomputed inverses: 1 / w^i
	domain.PreComputedInverses = make([]fr.Element, x)

	for i := uint64(0); i < x; i++ {
		domain.PreComputedInverses[i].Inverse(&domain.Roots[i])
	}

	return domain
}

func (d *Domain) ReverseRoots() {
	utils.BitReverse(d.Roots)
	utils.BitReverse(d.PreComputedInverses)
}

// Checks if a point is in the domain.
// TODO: this is on a hot path, so we should benchmark for faster
// TODO alternatives
func (d Domain) isInDomain(point fr.Element) bool {
	return d.findRootIndex(point) != -1
}

// Returns the index of the element in the domain or -1 if it
// is not an element in the domain
func (d Domain) findRootIndex(point fr.Element) int {
	for i := 0; i < int(d.Cardinality); i++ {
		if point.Equal(&d.Roots[i]) {
			return i
		}
	}
	return -1
}

func (domain *Domain) EvaluateLagrangePolynomial(poly Polynomial, eval_point fr.Element) (*fr.Element, error) {
	outputPoint, _, err := domain.evaluateLagrangePolynomial(poly, eval_point)
	return outputPoint, err
}

// TODO: possibly put this as a method on the domain instead
// Evaluates polynomial and returns the index iff the evaluation point
// was in the domain, -1 otherwise
// TODO: benchmark how long it takes to check if an element is in the domain
// TODO if its not a lot, we don't need to return the index here and just recompute
// TODO when we need it.
func (domain *Domain) evaluateLagrangePolynomial(poly Polynomial, eval_point fr.Element) (*fr.Element, int, error) {
	indexInDomain := -1

	if domain.Cardinality != uint64(len(poly)) {
		return nil, indexInDomain, errors.New("domain size does not equal the number of evaluations in the polynomial")
	}

	// If the evaluation point is in the domain
	// then evaluation of the polynomial in lagrange form
	// is the same as indexing it with the position
	// that the evaluation point is in, in the domain
	indexInDomain = domain.findRootIndex(eval_point)
	if indexInDomain != -1 {
		return &poly[indexInDomain], indexInDomain, nil
	}

	denom := make([]fr.Element, domain.Cardinality)
	for i := range denom {
		denom[i].Sub(&eval_point, &domain.Roots[i])
	}
	invDenom := fr.BatchInvert(denom)

	var result fr.Element
	for i := 0; i < int(domain.Cardinality); i++ {
		var num fr.Element
		num.Mul(&poly[i], &domain.Roots[i])

		var div fr.Element
		div.Mul(&num, &invDenom[i])

		result.Add(&result, &div)
	}

	// result * (x^width - 1) * 1/width
	var tmp fr.Element
	tmp.Exp(eval_point, big.NewInt(int64(domain.Cardinality)))
	one := fr.One()
	tmp.Sub(&tmp, &one)
	tmp.Mul(&tmp, &domain.CardinalityInv)
	result.Mul(&tmp, &result)

	return &result, indexInDomain, nil
}

func evaluateAllLagrangeCoefficients(domain Domain, tau fr.Element) []fr.Element {
	size := domain.Cardinality

	var t_size fr.Element
	t_size.Exp(tau, big.NewInt(int64(size)))

	one := fr.One()

	if t_size.IsOne() {
		u := make([]fr.Element, size)
		omega_i := one
		for i := uint64(0); i < size; i++ {
			if omega_i.Equal(&tau) {
				u[i] = one
			}
			omega_i.Mul(&omega_i, &domain.Generator)
		}
		return u
	} else {

		var l fr.Element
		l.Sub(&t_size, &one)
		l.Mul(&l, &domain.CardinalityInv)

		r := fr.One()
		u := make([]fr.Element, size)
		ls := make([]fr.Element, size)
		for i := uint64(0); i < size; i++ {
			u[i].Sub(&tau, &r)
			ls[i] = l
			l.Mul(&l, &domain.Generator)
			r.Mul(&r, &domain.Generator)
		}

		u = fr.BatchInvert(u)

		for i := uint64(0); i < size; i++ {
			u[i].Mul(&u[i], &ls[i])
		}
		return u
	}
}
