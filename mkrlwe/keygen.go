package mkrlwe

import (
	"math/big"

	"github.com/ldsec/lattigo/v2/ring"
	"github.com/ldsec/lattigo/v2/rlwe"
	"github.com/ldsec/lattigo/v2/utils"
)

// KeyGenerator is a structure that stores the elements required to create new keys,
// as well as a small memory pool for intermediate values.

// KeyGenerator is a structure that stores the elements required to create new keys,
// as well as a small memory pool for intermediate values.
type KeyGenerator struct {
	params             Parameters
	poolQ              *ring.Poly
	poolQP             rlwe.PolyQP
	gaussianSamplerQ   *ring.GaussianSampler
	NFgaussianSamplerQ *ring.GaussianSampler
	uniformSamplerQ    *ring.UniformSampler
	uniformSamplerP    *ring.UniformSampler
	ternarySampler     *ring.TernarySampler

	ringQ *ring.Ring
}

// NewKeyGenerator creates a new KeyGenerator, from which the secret and public keys, as well as the evaluation,
// rotation and switching keys can be generated.
func NewKeyGenerator(params Parameters) *KeyGenerator {

	ringQ := params.RingQ()

	prng, err := utils.NewPRNG()
	if err != nil {
		panic(err)
	}

	keygen := new(KeyGenerator)
	keygen.params = params
	keygen.poolQ = params.RingQ().NewPoly()
	keygen.poolQP = params.RingQP().NewPoly()
	keygen.gaussianSamplerQ = ring.NewGaussianSampler(prng, params.RingQ(), params.Sigma(), uint64(6*params.Sigma()))
	keygen.NFgaussianSamplerQ = ring.NewGaussianSampler(prng, params.RingQ(), params.Sigma(), uint64(6*params.Sigma()))
	keygen.uniformSamplerQ = ring.NewUniformSampler(prng, params.RingQ())
	keygen.uniformSamplerP = ring.NewUniformSampler(prng, params.RingP())

	keygen.ternarySampler = ring.NewTernarySampler(prng, ringQ, 0.5, false)

	return keygen
}

// genSecretKeyFromSampler generates a new SecretKey sampled from the provided Sampler.
// output SecretKey is in MForm
func (keygen *KeyGenerator) genSecretKeyFromSampler(sampler ring.Sampler, id string) *SecretKey {
	ringQP := keygen.params.RingQP()
	sk := new(SecretKey)
	sk.Value = ringQP.NewPoly()
	sk.ID = id
	levelQ, levelP := keygen.params.QCount()-1, keygen.params.PCount()-1
	sampler.Read(sk.Value.Q)
	ringQP.ExtendBasisSmallNormAndCenter(sk.Value.Q, levelP, nil, sk.Value.P)
	// fmt.Print("sk QP comparison = ", sk.Value.Q.Coeffs[1][2], sk.Value.P.Coeffs[1][2], "\n")
	ringQP.NTTLvl(levelQ, levelP, sk.Value, sk.Value)
	ringQP.MFormLvl(levelQ, levelP, sk.Value, sk.Value)
	return sk
}

// GenSecretKey generates a new SecretKey with the distribution [1/3, 1/3, 1/3].
func (keygen *KeyGenerator) GenSecretKey(id string) (sk *SecretKey) {
	return keygen.GenSecretKeyWithDistrib(1.0/2, id)
}

// GenSecretKey generates a new SecretKey with the error distribution.
func (keygen *KeyGenerator) GenSecretKeyGaussian(id string) (sk *SecretKey) {
	return keygen.genSecretKeyFromSampler(keygen.gaussianSamplerQ, id)
}

// GenSecretKeyWithDistrib generates a new SecretKey with the distribution [(p-1)/2, p, (p-1)/2].
func (keygen *KeyGenerator) GenSecretKeyWithDistrib(p float64, id string) (sk *SecretKey) {
	prng, err := utils.NewPRNG()
	if err != nil {
		panic(err)
	}
	ternarySamplerMontgomery := ring.NewTernarySampler(prng, keygen.params.RingQ(), p, false)
	return keygen.genSecretKeyFromSampler(ternarySamplerMontgomery, id)
}

// GenSecretKeySparse generates a new SecretKey with exactly hw non-zero coefficients.
func (keygen *KeyGenerator) GenSecretKeySparse(hw int, id string) (sk *SecretKey) {
	prng, err := utils.NewPRNG()
	if err != nil {
		panic(err)
	}
	ternarySamplerMontgomery := ring.NewTernarySamplerSparse(prng, keygen.params.RingQ(), hw, false)
	return keygen.genSecretKeyFromSampler(ternarySamplerMontgomery, id)
}

// GenPublicKey generates a new public key from the provided SecretKey.
func (keygen *KeyGenerator) GenPublicKey(sk *SecretKey) (pk *PublicKey) {

	pk = new(PublicKey)
	ringQP := keygen.params.RingQP()
	// ringQ := keygen.params.RingQ()
	levelQ, levelP := keygen.params.QCount()-1, keygen.params.PCount()-1

	id := sk.ID

	// sk = NewSecretKey(keygen.params, "group0")
	// ringQP.NTTLvl(levelQ, levelP, sk.Value, sk.Value)
	// ringQP.MFormLvl(levelQ, levelP, sk.Value, sk.Value)

	//pk[0] = [-as + e]
	//pk[1] = [a]
	pk = NewPublicKey(keygen.params, id)
	keygen.gaussianSamplerQ.Read(pk.Value[0].Q)
	ringQP.ExtendBasisSmallNormAndCenter(pk.Value[0].Q, levelP, nil, pk.Value[0].P)
	ringQP.NTTLvl(levelQ, levelP, pk.Value[0], pk.Value[0])
	// fmt.Print("pk error = ", pk.Value[0].Q.Coeffs[2][3], "\n")

	//set a to CRS[0][0]
	pk.Value[1].Q.Copy(keygen.params.CRS[0].Value[0].Q)
	pk.Value[1].P.Copy(keygen.params.CRS[0].Value[0].P)
	// pk.Value[1].Q = keygen.params.CRS[0].Value[0].Q
	// pk.Value[1].P = keygen.params.CRS[0].Value[0].P
	// ringQP.ExtendBasisSmallNormAndCenter(pk.Value[1].Q, levelP, pk.Value[1].Q, pk.Value[1].P)
	// pk.Value[1].P.Copy(keygen.params.CRS[0].Value[0].P)

	ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, sk.Value, pk.Value[1], pk.Value[0])
	return pk
}

// GenKeyPair generates a new SecretKey with distribution [1/3, 1/3, 1/3] and a corresponding public key.
func (keygen *KeyGenerator) GenKeyPair(id string) (sk *SecretKey, pk *PublicKey) {
	sk = keygen.GenSecretKey(id)
	return sk, keygen.GenPublicKey(sk)
}

// GenKeyPairSparse generates a new SecretKey with exactly hw non zero coefficients [1/2, 0, 1/2].
func (keygen *KeyGenerator) GenKeyPairSparse(hw int) (sk *SecretKey, pk *PublicKey) {
	sk = keygen.GenSecretKeySparse(hw, sk.ID)
	return sk, keygen.GenPublicKey(sk)
}

func (keygen *KeyGenerator) GenGaussianError(e rlwe.PolyQP) {

	levelQ := keygen.params.QCount() - 1
	levelP := keygen.params.PCount() - 1
	ringQP := keygen.params.RingQP()

	keygen.gaussianSamplerQ.ReadLvl(levelQ, e.Q)
	ringQP.ExtendBasisSmallNormAndCenter(e.Q, levelP, nil, e.P)
	ringQP.NTTLvl(levelQ, levelP, e, e)

}

// GenRelinKey generates a new EvaluationKey that will be used to relinearize Ciphertexts during multiplication.
// RelinearizationKeys are triplet of polyvector in  MontgomeryForm
func (keygen *KeyGenerator) GenRelinearizationKey(sk *SecretKey) (rlk *RelinearizationKey) {

	if keygen.params.PCount() == 0 {
		panic("modulus P is empty")
	}
	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	ringQP := params.RingQP()
	ringQ := params.RingQ()
	ringP := params.RingP()

	id := sk.ID

	//rlk = (b, d, v)
	rlk = NewRelinearizationKey(keygen.params, id)
	beta := params.Beta(levelQ)

	//set CRS
	a := keygen.params.CRS[0]
	u := keygen.params.CRS[-1]
	r := keygen.GenSecretKey(id)

	tmp := keygen.poolQP

	//generate vector b = -sa + e in MForm
	b := rlk.Value[0]
	for i := 0; i < beta; i++ {
		ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, a.Value[i], sk.Value, b.Value[i])
		ringQP.InvMFormLvl(levelQ, levelP, b.Value[i], b.Value[i])
		keygen.GenGaussianError(tmp)
		ringQP.SubLvl(levelQ, levelP, tmp, b.Value[i], b.Value[i])
		ringQP.MFormLvl(levelQ, levelP, b.Value[i], b.Value[i])
	}

	//generate vector d = -ra + sg + e in MForm
	d := rlk.Value[1]
	keygen.GenSwitchingKey(sk, d)
	for i := 0; i < beta; i++ {
		ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, a.Value[i], r.Value, d.Value[i])
	}

	//generate vector v = -su - rg + e in MForm
	v := rlk.Value[2]
	keygen.GenSwitchingKey(r, v)
	for i := 0; i < beta; i++ {
		ringQP.MulCoeffsMontgomeryAndAddLvl(levelQ, levelP, u.Value[i], sk.Value, v.Value[i])
		ringQ.NegLvl(levelQ, v.Value[i].Q, v.Value[i].Q)
		ringP.NegLvl(levelP, v.Value[i].P, v.Value[i].P)
	}
	return
}

// GenRotationKeys generates a RotationKeySet from a list of galois element corresponding to the desired rotations
func (keygen *KeyGenerator) GenRotationKey(rotidx int, sk *SecretKey) (rk *RotationKey) {
	skIn := sk
	id := sk.ID
	skOut := NewSecretKey(keygen.params, id)

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)
	ringQP := params.RingQP()

	// check CRS for given rot idx exists
	_, in := params.CRS[rotidx]
	if !in {
		panic("Cannot GenRotationKey: CRS for given rot idx is not generated")
	}

	// adjust rotidx
	for rotidx < 0 {
		rotidx += (params.N() / 2)
	}

	galEl := keygen.params.GaloisElementForColumnRotationBy(rotidx)
	galEl = keygen.params.InverseGaloisElement(galEl)
	index := ring.PermuteNTTIndex(galEl, uint64(params.N()))
	ring.PermuteNTTWithIndexLvl(params.QCount()-1, skIn.Value.Q, index, skOut.Value.Q)
	ring.PermuteNTTWithIndexLvl(params.PCount()-1, skIn.Value.P, index, skOut.Value.P)

	// rk  = Ps + e
	rk = NewRotationKey(params, uint(rotidx), id)
	keygen.GenSwitchingKey(skIn, rk.Value)
	a := params.CRS[rotidx]

	// rk = -s'a + Ps' + e
	for i := 0; i < beta; i++ {
		ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, a.Value[i], skOut.Value, rk.Value.Value[i])
	}

	return rk
}

// GenRotationKeys generates a RotationKeys of rotidx power of 2 and add it to rtkList
func (keygen *KeyGenerator) GenDefaultRotationKeys(sk *SecretKey) (rtks map[uint]*RotationKey) {
	rtks = make(map[uint]*RotationKey)

	for rotidx := 1; rotidx < 2; rotidx *= 2 { // 수정
		rtk := keygen.GenRotationKey(rotidx, sk)
		rtks[uint(rotidx)] = rtk
	}

	return rtks
}

// GenConjugationKeys generates a ConjugationKeySet from a list of galois element corresponding to the desired conjugation
func (keygen *KeyGenerator) GenConjugationKey(sk *SecretKey) (cjk *ConjugationKey) {
	skIn := sk
	id := sk.ID
	skOut := NewSecretKey(keygen.params, id)

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)
	ringQP := params.RingQP()

	galEl := keygen.params.GaloisElementForRowRotation()
	index := ring.PermuteNTTIndex(galEl, uint64(params.N()))
	ring.PermuteNTTWithIndexLvl(params.QCount()-1, skIn.Value.Q, index, skOut.Value.Q)
	ring.PermuteNTTWithIndexLvl(params.PCount()-1, skIn.Value.P, index, skOut.Value.P)

	// rk  = Ps' + e
	cjk = NewConjugationKey(params, id)
	keygen.GenSwitchingKey(skOut, cjk.Value)
	a := params.CRS[-2]

	// rk = -sa + Ps' + e
	for i := 0; i < beta; i++ {
		ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, a.Value[i], sk.Value, cjk.Value.Value[i])
	}
	return cjk
}

// For an input secretkey s, gen gs + e in MForm
func (keygen *KeyGenerator) GenSwitchingKey(skIn *SecretKey, swk *SwitchingKey) {
	params := keygen.params
	ringQ := params.RingQ()
	levelQ, levelP := params.QCount()-1, params.PCount()-1
	alpha := params.Alpha()
	beta := params.Beta(levelQ)
	// fmt.Print("beta = ", beta, "\n")

	var pBigInt *big.Int
	if levelP == keygen.params.PCount()-1 {
		pBigInt = keygen.params.RingP().ModulusBigint
	} else {
		P := keygen.params.RingP().Modulus
		pBigInt = new(big.Int).SetUint64(P[0])
		for i := 1; i < levelP+1; i++ {
			pBigInt.Mul(pBigInt, ring.NewUint(P[i]))
		}
	}

	// Computes P * skIn
	ringQ.MulScalarBigintLvl(levelQ, skIn.Value.Q, pBigInt, keygen.poolQ)

	var index int
	for i := 0; i < beta; i++ {

		// e

		ringQP := params.RingQP()

		keygen.gaussianSamplerQ.ReadLvl(levelQ, swk.Value[i].Q)
		swk.Value[i].Q.Zero() // 에러 없애기
		ringQP.ExtendBasisSmallNormAndCenter(swk.Value[i].Q, levelP, nil, swk.Value[i].P)

		ringQP.NTTLvl(levelQ, levelP, swk.Value[i], swk.Value[i])
		ringQP.MFormLvl(levelQ, levelP, swk.Value[i], swk.Value[i])
		// e + (skIn * P) * (q_star * q_tild) mod QP
		//
		// q_prod = prod(q[i*alpha+j])
		// q_star = Q/qprod
		// q_tild = q_star^-1 mod q_prod
		//
		// Therefore : (skIn * P) * (q_star * q_tild) = sk*P mod q[i*alpha+j], else 0
		for j := 0; j < alpha; j++ {

			index = i*alpha + j

			// It handles the case where nb pj does not divide nb qi
			if index >= levelQ+1 {
				break
			}

			qi := ringQ.Modulus[index]
			p0tmp := keygen.poolQ.Coeffs[index]
			p1tmp := swk.Value[i].Q.Coeffs[index]

			for w := 0; w < ringQ.N; w++ {
				p1tmp[w] = ring.CRed(p1tmp[w]+p0tmp[w], qi)
			}
		}
	}
}

// GenConjugationKeys generates a ConjugationKeySet from a list of galois element corresponding to the desired conjugation
func (keygen *KeyGenerator) GenSWKTest(sk *SecretKey, sk2 *SecretKey) (swk *SWK, swkhead *SWK) {
	// skIn := sk
	id := sk.ID
	// skOut := NewSecretKey(keygen.params, id)

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)
	ringQP := params.RingQP()

	// Reset sk to zero
	// sk = NewSecretKey(params, "group0")
	ringQP.InvMFormLvl(levelQ, levelP, sk.Value, sk.Value)

	// rk  = Ps' + e
	swk = NewSWK(params, id)
	swkhead = NewSWK(params, id)
	keygen.GenSwitchingKey(sk, swk.Value)

	for i := 0; i < beta; i++ {
		r0 := ringQP.NewPoly()
		keygen.gaussianSamplerQ.ReadLvl(levelQ, r0.Q)
		ringQP.ExtendBasisSmallNormAndCenter(r0.Q, levelP, r0.Q, r0.P)
		ringQP.NTTLvl(levelQ, levelP, r0, r0)

		r1 := ringQP.NewPoly()
		keygen.gaussianSamplerQ.ReadLvl(levelQ, r1.Q)
		ringQP.ExtendBasisSmallNormAndCenter(r1.Q, levelP, r1.Q, r1.P)
		ringQP.NTTLvl(levelQ, levelP, r1, r1)

		r2 := ringQP.NewPoly()
		keygen.ternarySampler.ReadLvl(levelQ, r2.Q)
		ringQP.ExtendBasisSmallNormAndCenter(r2.Q, levelP, r2.Q, r2.P)
		ringQP.NTTLvl(levelQ, levelP, r2, r2)

		a := ringQP.NewPoly()
		keygen.uniformSamplerQ.ReadLvl(levelQ, a.Q)
		keygen.uniformSamplerP.ReadLvl(levelP, a.P)
		ringQP.NTTLvl(levelQ, levelP, a, a)

		e1 := ringQP.NewPoly()
		keygen.gaussianSamplerQ.ReadLvl(levelQ, e1.Q)
		ringQP.ExtendBasisSmallNormAndCenter(e1.Q, levelP, e1.Q, e1.P) // 필요!
		ringQP.NTTLvl(levelQ, levelP, e1, e1)                          // 필요!

		b := ringQP.NewPoly()
		ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, a, sk2.Value, b)
		ringQP.SubLvl(levelQ, levelP, e1, b, b)

		ringQP.MFormLvl(levelQ, levelP, a, swkhead.Value.Value[i])
		ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, swkhead.Value.Value[i], r2, swkhead.Value.Value[i])
		ringQP.AddLvl(levelQ, levelP, swkhead.Value.Value[i], r1, swkhead.Value.Value[i])

		ringQP.MFormLvl(levelQ, levelP, b, b)
		ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, b, r2, b)
		ringQP.AddLvl(levelQ, levelP, swk.Value.Value[i], b, swk.Value.Value[i])
		ringQP.AddLvl(levelQ, levelP, swk.Value.Value[i], r0, swk.Value.Value[i])

		ringQP.MFormLvl(levelQ, levelP, swk.Value.Value[i], swk.Value.Value[i])
		ringQP.MFormLvl(levelQ, levelP, swkhead.Value.Value[i], swkhead.Value.Value[i])
	}
	// fmt.Print("swkhead = ", swkhead.Value.Value[0].Q.Coeffs[4][5], "\n")
	ringQP.MFormLvl(levelQ, levelP, sk.Value, sk.Value)
	return swk, swkhead
}

func (keygen *KeyGenerator) UAuxKeyGen(swkheadsum *SWK, sk *SecretKey) (uaux *SWK, uauxhead *SWK) {

	id := sk.ID

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)
	ringQP := params.RingQP()

	uaux = NewSWK(params, id)
	uauxhead = NewSWK(params, id)

	ringQP.InvMFormLvl(levelQ, levelP, sk.Value, sk.Value)

	for i := 0; i < beta; i++ {
		e := ringQP.NewPoly()
		keygen.NFgaussianSamplerQ.ReadLvl(levelQ, e.Q)
		ringQP.ExtendBasisSmallNormAndCenter(e.Q, levelP, e.Q, e.P)
		ringQP.NTTLvl(levelQ, levelP, e, e)

		b := ringQP.NewPoly()
		ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, swkheadsum.Value.Value[i], sk.Value, b)
		ringQP.SubLvl(levelQ, levelP, e, b, uaux.Value.Value[i])

		uauxhead.Value.Value[i].Q.Copy(swkheadsum.Value.Value[i].Q)
		uauxhead.Value.Value[i].P.Copy(swkheadsum.Value.Value[i].P)

		ringQP.MFormLvl(levelQ, levelP, uaux.Value.Value[i], uaux.Value.Value[i])
		ringQP.MFormLvl(levelQ, levelP, uauxhead.Value.Value[i], uauxhead.Value.Value[i])
	}
	// fmt.Print("swkhead = ", swkhead.Value.Value[0].Q.Coeffs[4][5], "\n")
	ringQP.MFormLvl(levelQ, levelP, sk.Value, sk.Value)
	return uaux, uauxhead
}

// GenPublicKey generates a new public key from the provided SecretKey.
func (keygen *KeyGenerator) GenSWK(sk *SecretKey, pk *PublicKey) (swk *SWK, swkhead *SWK) {
	// skIn := sk
	id := sk.ID
	// skOut := NewSecretKey(keygen.params, id)

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)
	ringQP := params.RingQP()

	// ringQ := params.RingQ()
	// ringP := params.RingP()

	// Reset sk to zero
	// zsk := NewSecretKey(params, "group0")
	ringQP.InvMFormLvl(levelQ, levelP, sk.Value, sk.Value)

	// rk  = Ps' + e
	swk = NewSWK(params, id)
	swkhead = NewSWK(params, id)
	keygen.GenSwitchingKey(sk, swk.Value)

	a := ringQP.NewPoly()
	b := ringQP.NewPoly()
	ringQP.NTTLvl(levelQ, levelP, a, a)

	for i := 0; i < beta; i++ {
		b.Q.Copy(pk.Value[0].Q) // ringQP.NewPoly()
		b.P.Copy(pk.Value[0].P)
		a.Q.Copy(pk.Value[1].Q)
		a.P.Copy(pk.Value[1].P)

		r0 := ringQP.NewPoly()
		keygen.gaussianSamplerQ.ReadLvl(levelQ, r0.Q)
		ringQP.ExtendBasisSmallNormAndCenter(r0.Q, levelP, r0.Q, r0.P)
		ringQP.NTTLvl(levelQ, levelP, r0, r0)

		r1 := ringQP.NewPoly()
		keygen.gaussianSamplerQ.ReadLvl(levelQ, r1.Q)
		ringQP.ExtendBasisSmallNormAndCenter(r1.Q, levelP, r1.Q, r1.P)
		ringQP.NTTLvl(levelQ, levelP, r1, r1)

		r2 := ringQP.NewPoly()
		keygen.ternarySampler.ReadLvl(levelQ, r2.Q)
		ringQP.ExtendBasisSmallNormAndCenter(r2.Q, levelP, r2.Q, r2.P)
		ringQP.NTTLvl(levelQ, levelP, r2, r2)

		/////////////

		ringQP.MFormLvl(levelQ, levelP, a, swkhead.Value.Value[i])
		ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, swkhead.Value.Value[i], r2, swkhead.Value.Value[i])
		ringQP.AddLvl(levelQ, levelP, swkhead.Value.Value[i], r1, swkhead.Value.Value[i])

		ringQP.MFormLvl(levelQ, levelP, b, b)
		ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, b, r2, b)
		ringQP.AddLvl(levelQ, levelP, swk.Value.Value[i], b, swk.Value.Value[i])
		ringQP.AddLvl(levelQ, levelP, swk.Value.Value[i], r0, swk.Value.Value[i])

		ringQP.MFormLvl(levelQ, levelP, swk.Value.Value[i], swk.Value.Value[i])
		ringQP.MFormLvl(levelQ, levelP, swkhead.Value.Value[i], swkhead.Value.Value[i])

		// ringQP.MulCoeffsMontgomeryAndAddLvl(levelQ, levelP, r0, pk.Value[0], swk.Value.Value[i])
		// ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, r0, pk.Value[1], swkhead.Value.Value[i])
		// // ringQP.NTTLvl(levelQ, levelP, swkhead.Value.Value[i], swkhead.Value.Value[i])
		// ringQP.AddLvl(levelQ, levelP, e1, swkhead.Value.Value[i], swkhead.Value.Value[i])

		// ringQ.MulCoeffsMontgomeryAndAddLvl(levelQ, r0.Q, pk.Value[0].Q, swk.Value.Value[i].Q)
		// ringQ.MulCoeffsMontgomeryLvl(levelQ, r0.Q, pk.Value[1].Q, swkhead.Value.Value[i].Q)
		// // ringQ.NTTLvl(levelQ, swkhead.Value.Value[i].Q, swkhead.Value.Value[i].Q)
		// ringQ.AddLvl(levelQ, e1.Q, swkhead.Value.Value[i].Q, swkhead.Value.Value[i].Q)

		// ringP.MulCoeffsMontgomeryAndAddLvl(levelP, r0.P, pk.Value[0].P, swk.Value.Value[i].P)
		// ringP.MulCoeffsMontgomeryAndAddLvl(levelP, r0.P, pk.Value[1].P, swkhead.Value.Value[i].P)
		// // ringP.NTTLvl(levelP, swkhead.Value.Value[i].P, swkhead.Value.Value[i].P)
		// ringP.AddLvl(levelP, e1.P, swkhead.Value.Value[i].P, swkhead.Value.Value[i].P)

		// ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, pk.Value[1], r0, swkhead.Value.Value[i])
	}
	ringQP.MFormLvl(levelQ, levelP, sk.Value, sk.Value)
	// fmt.Print("pk0 after = ", pk.Value[0].Q.Coeffs[2][3], "\n")
	// fmt.Print("pk1 after = ", pk.Value[1].Q.Coeffs[2][3], "\n")

	// ringQP.InvMFormLvl(levelQ, levelP, pk.Value[0], pk.Value[0])
	// ringQP.InvMFormLvl(levelQ, levelP, pk.Value[1], pk.Value[1])
	// ringQP.InvNTTLvl(levelQ, levelP, pk.Value[0], pk.Value[0])
	// ringQP.InvNTTLvl(levelQ, levelP, pk.Value[1], pk.Value[1])

	return swk, swkhead
}

// aggreagate secret keys in multi party setting
func (keygen *KeyGenerator) GenGroupSecretKey(skList []*SecretKey) (skOut *SecretKey) {

	if len(skList) == 0 {
		panic("invalid input: empty secretkey list")
	}

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1

	id := skList[0].ID
	skOut = NewSecretKey(params, id)

	for _, sk := range skList {
		if id != sk.ID {
			panic("invalid input: IDs are not same")
		}

		params.RingQP().AddLvl(levelQ, levelP, skOut.Value, sk.Value, skOut.Value)
	}

	return skOut
}

// aggregate public encryption keys
func (keygen *KeyGenerator) GenGroupPublicKey(pkList []*PublicKey) (pkOut *PublicKey) {

	if len(pkList) == 0 {
		panic("invalid input: empty publickey list")
	}

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1

	id := pkList[0].ID
	pkOut = NewPublicKey(params, id)

	for _, pk := range pkList {
		if id != pk.ID {
			panic("invalid input: IDs are not same")
		}

		params.RingQP().AddLvl(levelQ, levelP, pkOut.Value[0], pk.Value[0], pkOut.Value[0])
	}

	params.RingQP().AddLvl(levelQ, levelP, pkOut.Value[1], pkList[0].Value[1], pkOut.Value[1])

	return pkOut
}

func (keygen *KeyGenerator) GenGroupRotKey(rtkList []*RotationKey) (rtkOut *RotationKey) {

	if len(rtkList) == 0 {
		panic("invalid input: empty rotkey list")
	}

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)

	id := rtkList[0].ID
	idx := rtkList[0].RotIdx
	rtkOut = NewRotationKey(params, idx, id)

	for _, rtk := range rtkList {
		if id != rtk.ID {
			panic("invalid input: IDs are not same")
		}

		if idx != rtk.RotIdx {
			panic("invalid input: rotation indexes are not same")
		}

		for i := 0; i < beta; i++ {
			params.RingQP().AddLvl(levelQ, levelP, rtk.Value.Value[i], rtkOut.Value.Value[i], rtkOut.Value.Value[i])
		}
	}

	return rtkOut
}

func (keygen *KeyGenerator) GenGroupConjKey(cjkList []*ConjugationKey) (cjkOut *ConjugationKey) {

	if len(cjkList) == 0 {
		panic("invalid input: empty conjkey list")
	}

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)

	id := cjkList[0].ID
	cjkOut = NewConjugationKey(params, id)

	for _, cjk := range cjkList {
		if id != cjk.ID {
			panic("invalid input: IDs are not same")
		}

		for i := 0; i < beta; i++ {
			params.RingQP().AddLvl(levelQ, levelP, cjk.Value.Value[i], cjkOut.Value.Value[i], cjkOut.Value.Value[i])
		}
	}
	return cjkOut
}

func (keygen *KeyGenerator) GenGroupSWK(swkList []*SWK) (swkOut *SWK) {

	if len(swkList) == 0 {
		panic("invalid input: empty conjkey list")
	}

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)

	id := swkList[0].ID
	swkOut = NewSWK(params, id)

	for _, swk := range swkList {
		if id != swk.ID {
			panic("invalid input: IDs are not same")
		}

		for i := 0; i < beta; i++ {
			params.RingQP().AddLvl(levelQ, levelP, swk.Value.Value[i], swkOut.Value.Value[i], swkOut.Value.Value[i])
		}
	}
	return swkOut
}

func (keygen *KeyGenerator) GenGroupRelinKey(rlkList []*RelinearizationKey) (rlkOut *RelinearizationKey) {
	if len(rlkList) == 0 {
		panic("invalid input: empty relinkey list")
	}

	params := keygen.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)

	id := rlkList[0].ID
	rlkOut = NewRelinearizationKey(params, id)

	for _, rlk := range rlkList {
		if id != rlk.ID {
			panic("invalid input: IDs are not same")
		}

		for i := 0; i < beta; i++ {
			params.RingQP().AddLvl(levelQ, levelP, rlk.Value[0].Value[i], rlkOut.Value[0].Value[i], rlkOut.Value[0].Value[i])
			params.RingQP().AddLvl(levelQ, levelP, rlk.Value[1].Value[i], rlkOut.Value[1].Value[i], rlkOut.Value[1].Value[i])
			params.RingQP().AddLvl(levelQ, levelP, rlk.Value[2].Value[i], rlkOut.Value[2].Value[i], rlkOut.Value[2].Value[i])
		}
	}

	return rlkOut
}
