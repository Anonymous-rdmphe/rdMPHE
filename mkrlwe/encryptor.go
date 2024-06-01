package mkrlwe

import (
	"github.com/ldsec/lattigo/v2/ring"
	"github.com/ldsec/lattigo/v2/rlwe"
	"github.com/ldsec/lattigo/v2/utils"
)

// encryptorBase is a struct used to encrypt Plaintexts. It stores the public-key and/or secret-key.
type encryptorBase struct {
	params Parameters

	ringQ *ring.Ring
	ringP *ring.Ring

	poolQ [1]*ring.Poly
	poolP [3]*ring.Poly

	gaussianSampler *ring.GaussianSampler
	ternarySampler  *ring.TernarySampler
	uniformSampler  *ring.UniformSampler
}

// Encryptor is a struct used to encrypt plaintext with public key
type Encryptor struct {
	encryptorBase
}

func newEncryptorBase(params Parameters) encryptorBase {

	ringQ := params.RingQ()
	ringP := params.RingP()

	prng, err := utils.NewPRNG()
	if err != nil {
		panic(err)
	}

	var poolP [3]*ring.Poly
	if params.PCount() != 0 {
		poolP = [3]*ring.Poly{ringP.NewPoly(), ringP.NewPoly(), ringP.NewPoly()}
	}

	return encryptorBase{
		params:          params,
		ringQ:           ringQ,
		ringP:           ringP,
		poolQ:           [1]*ring.Poly{ringQ.NewPoly()},
		poolP:           poolP,
		gaussianSampler: ring.NewGaussianSampler(prng, ringQ, params.Sigma(), uint64(6*params.Sigma())),
		ternarySampler:  ring.NewTernarySampler(prng, ringQ, 0.5, false),
		uniformSampler:  ring.NewUniformSampler(prng, ringQ),
	}
}

// Encrypt encrypts the input Plaintext and write the result in ctOut.
func (encryptor *Encryptor) Encrypt(plaintext *rlwe.Plaintext, pk *PublicKey, ctOut *Ciphertext) {
	id := pk.ID
	levelQ := utils.MinInt(plaintext.Level(), ctOut.Level())

	poolQ0 := encryptor.poolQ[0]

	ringQ := encryptor.ringQ

	ciphertextNTT := ctOut.Value["0"].IsNTT

	encryptor.ternarySampler.ReadLvl(levelQ, poolQ0)
	ringQ.NTTLvl(levelQ, poolQ0, poolQ0)
	ringQ.MFormLvl(levelQ, poolQ0, poolQ0)

	// ct0 = u*pk0
	ringQ.MulCoeffsMontgomeryLvl(levelQ, poolQ0, pk.Value[0].Q, ctOut.Value["0"])
	// ct1 = u*pk1
	ringQ.MulCoeffsMontgomeryLvl(levelQ, poolQ0, pk.Value[1].Q, ctOut.Value[id])

	if ciphertextNTT {

		// ct1 = u*pk1 + e1
		encryptor.gaussianSampler.ReadLvl(levelQ, poolQ0)
		ringQ.NTTLvl(levelQ, poolQ0, poolQ0)
		ringQ.AddLvl(levelQ, ctOut.Value[id], poolQ0, ctOut.Value[id])

		// ct0 = u*pk0 + e0
		encryptor.gaussianSampler.ReadLvl(levelQ, poolQ0)

		if !plaintext.Value.IsNTT {
			ringQ.AddLvl(levelQ, poolQ0, plaintext.Value, poolQ0)
			ringQ.NTTLvl(levelQ, poolQ0, poolQ0)
			ringQ.AddLvl(levelQ, ctOut.Value["0"], poolQ0, ctOut.Value["0"])
		} else {
			ringQ.NTTLvl(levelQ, poolQ0, poolQ0)
			ringQ.AddLvl(levelQ, ctOut.Value["0"], poolQ0, ctOut.Value["0"])
			ringQ.AddLvl(levelQ, ctOut.Value["0"], plaintext.Value, ctOut.Value["0"])
		}

	} else {

		ringQ.InvNTTLvl(levelQ, ctOut.Value["0"], ctOut.Value["0"])
		ringQ.InvNTTLvl(levelQ, ctOut.Value[id], ctOut.Value[id])

		// ct[0] = pk[0]*u + e0
		encryptor.gaussianSampler.ReadAndAddLvl(ctOut.Level(), ctOut.Value["0"])

		// ct[1] = pk[1]*u + e1
		encryptor.gaussianSampler.ReadAndAddLvl(ctOut.Level(), ctOut.Value[id])

		if !plaintext.Value.IsNTT {
			ringQ.AddLvl(levelQ, ctOut.Value["0"], plaintext.Value, ctOut.Value["0"])
		} else {
			ringQ.InvNTTLvl(levelQ, plaintext.Value, poolQ0)
			ringQ.AddLvl(levelQ, ctOut.Value["0"], poolQ0, ctOut.Value["0"])
		}
	}

	ctOut.Value[id].IsNTT = ctOut.Value["0"].IsNTT

	ctOut.Value["0"].Coeffs = ctOut.Value["0"].Coeffs[:levelQ+1]
	ctOut.Value[id].Coeffs = ctOut.Value[id].Coeffs[:levelQ+1]

}

// EncryptSk encrypts the input Plaintext with sk and write the result in ctOut.
func (encryptor *Encryptor) EncryptSk(plaintext *rlwe.Plaintext, sk *SecretKey, ctOut *Ciphertext) {
	id := sk.ID
	levelQ := utils.MinInt(plaintext.Level(), ctOut.Level())

	poolQ0 := encryptor.poolQ[0]

	ringQ := encryptor.ringQ

	ciphertextNTT := ctOut.Value["0"].IsNTT

	encryptor.uniformSampler.ReadLvl(levelQ, poolQ0)
	ringQ.NTTLvl(levelQ, poolQ0, poolQ0)
	ringQ.MFormLvl(levelQ, poolQ0, poolQ0)

	// ct0 = u*sk
	ringQ.MulCoeffsMontgomeryLvl(levelQ, poolQ0, sk.Value.Q, ctOut.Value["0"])
	// ct1 = u
	ctOut.Value[id] = poolQ0

	if ciphertextNTT {

		// ct1 = u*pk1 + e1
		// encryptor.gaussianSampler.ReadLvl(levelQ, poolQ0)
		// ringQ.NTTLvl(levelQ, poolQ0, poolQ0)
		// ringQ.AddLvl(levelQ, ctOut.Value[id], poolQ0, ctOut.Value[id])

		encryptor.gaussianSampler.ReadLvl(levelQ, poolQ0)

		if !plaintext.Value.IsNTT {
			// E = e + ptxt
			ringQ.AddLvl(levelQ, poolQ0, plaintext.Value, poolQ0)
			ringQ.NTTLvl(levelQ, poolQ0, poolQ0)
			// ct0 = (e + ptxt) - u*sk
			ringQ.SubLvl(levelQ, poolQ0, ctOut.Value["0"], ctOut.Value["0"])
		} else {
			ringQ.NTTLvl(levelQ, poolQ0, poolQ0)
			// e - u*sk
			ringQ.SubLvl(levelQ, poolQ0, ctOut.Value["0"], ctOut.Value["0"])
			// ct0 = (e - u*sk) + ptxt
			ringQ.AddLvl(levelQ, ctOut.Value["0"], plaintext.Value, ctOut.Value["0"])
		}
		// ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, sk.Value, pk.Value[1], pk.Value[0])
	} else {

		ringQ.InvNTTLvl(levelQ, ctOut.Value["0"], ctOut.Value["0"])
		ringQ.InvNTTLvl(levelQ, ctOut.Value[id], ctOut.Value[id])

		// ct[0] = e0 + u*sk
		encryptor.gaussianSampler.ReadAndAddLvl(ctOut.Level(), ctOut.Value["0"])

		// ct[1] = pk[1]*u + e1
		// encryptor.gaussianSampler.ReadAndAddLvl(ctOut.Level(), ctOut.Value[id])

		if !plaintext.Value.IsNTT {
			// ct0 = ptxt - (e0 + u*sk)
			ringQ.SubLvl(levelQ, plaintext.Value, ctOut.Value["0"], ctOut.Value["0"])
		} else {
			ringQ.InvNTTLvl(levelQ, plaintext.Value, poolQ0)
			// ct0 = ptxt - (e0 + u*sk)
			ringQ.SubLvl(levelQ, poolQ0, ctOut.Value["0"], ctOut.Value["0"])
		}
	}

	ctOut.Value[id].IsNTT = ctOut.Value["0"].IsNTT

	ctOut.Value["0"].Coeffs = ctOut.Value["0"].Coeffs[:levelQ+1]
	ctOut.Value[id].Coeffs = ctOut.Value[id].Coeffs[:levelQ+1]

}

// 	id := sk.ID
// 	levelQ := utils.MinInt(plaintext.Level(), ctOut.Level())

// 	poolQ0 := encryptor.poolQ[0]

// 	ringQ := encryptor.ringQ

// 	// ciphertextNTT := ctOut.Value["0"].IsNTT

// 	// encryptor.ternarySampler.ReadLvl(levelQ, poolQ0)
// 	// ringQ.NTTLvl(levelQ, poolQ0, poolQ0)
// 	// ringQ.MFormLvl(levelQ, poolQ0, poolQ0)

// 	// ct0 = u*sk
// 	ringQ.MulCoeffsMontgomeryAndSubLvl(levelQ, poolQ0, sk.Value.Q, ctOut.Value["0"])
// 	ctOut.Value[id] = poolQ0
// 	// // ct1 = u*pk1
// 	// ringQ.MulCoeffsMontgomeryLvl(levelQ, poolQ0, sk.Value.Q, ctOut.Value[id])

// 	ringQ.InvNTTLvl(levelQ, ctOut.Value["0"], ctOut.Value["0"])
// 	ringQ.InvNTTLvl(levelQ, ctOut.Value[id], ctOut.Value[id])

// 	// ct[0] = ct[0] + e0
// 	encryptor.gaussianSampler.ReadAndAddLvl(ctOut.Level(), ctOut.Value["0"])

// 	// // ct[1] = ct[1] + e1
// 	// encryptor.gaussianSampler.ReadAndAddLvl(ctOut.Level(), ctOut.Value[id])

// 	if !plaintext.Value.IsNTT {
// 		ringQ.AddLvl(levelQ, ctOut.Value["0"], plaintext.Value, ctOut.Value["0"])
// 	} else {
// 		ringQ.InvNTTLvl(levelQ, plaintext.Value, poolQ0)
// 		ringQ.AddLvl(levelQ, ctOut.Value["0"], poolQ0, ctOut.Value["0"])
// 	}
// 	ctOut.Value[id].IsNTT = ctOut.Value["0"].IsNTT

// 	ctOut.Value["0"].Coeffs = ctOut.Value["0"].Coeffs[:levelQ+1]
// 	ctOut.Value[id].Coeffs = ctOut.Value[id].Coeffs[:levelQ+1]
// }

// NewEncryptor instatiates a new generic RLWE Encryptor. The key argument can
// be either a *rlwe.PublicKey or a *rlwe.SecretKey.
func NewEncryptor(params Parameters) *Encryptor {
	return &Encryptor{newEncryptorBase(params)}
}
