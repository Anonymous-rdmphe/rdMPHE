package mkrlwe

import (
	"github.com/ldsec/lattigo/v2/ring"
	"github.com/ldsec/lattigo/v2/rlwe"
	"github.com/ldsec/lattigo/v2/utils"
	// "fmt"
)

// decryptor is a structure used to decrypt ciphertext. It stores the secret-key.
type Decryptor struct {
	params             Parameters
	ringQ              *ring.Ring
	pool               *ring.Poly
	sk                 *SecretKey
	NFgaussianSamplerQ *ring.GaussianSampler
}

// NewDecryptor instantiates a new generic RLWE Decryptor.
func NewDecryptor(params Parameters) *Decryptor {
	prng, _ := utils.NewPRNG()
	return &Decryptor{
		params:             params,
		ringQ:              params.RingQ(),
		pool:               params.RingQ().NewPoly(),
		NFgaussianSamplerQ: ring.NewGaussianSampler(prng, params.RingQ(), (params.Sigma()), uint64(6*params.Sigma())),
		// 2^70 = 1180591620717411303424
		// 2^64 = 18446744073709551616
		// 2^40 = 1099511627776
	}
}

// PartialDecrypt partially decrypts the ct with single secretkey sk and update result inplace
func (decryptor *Decryptor) PartialDecryptOriginal(ct *Ciphertext, sk *SecretKey) {
	ringQ := decryptor.ringQ
	id := sk.ID
	level := ct.Level()

	if !ct.Value[id].IsNTT {
		ringQ.NTTLvl(level, ct.Value[id], ct.Value[id])
	}

	ringQ.MulCoeffsMontgomeryLvl(level, ct.Value[id], sk.Value.Q, ct.Value[id])

	if !ct.Value[id].IsNTT {
		ringQ.InvNTTLvl(level, ct.Value[id], ct.Value[id])
	}

	ringQ.AddLvl(level, ct.Value["0"], ct.Value[id], ct.Value["0"])
	// delete(ct.Value, id)
}

// PartialDecrypt partially decrypts the ct with single secretkey sk and update result inplace
func (decryptor *Decryptor) PartialDecrypt(ct *Ciphertext, sk *SecretKey) {
	ringQ := decryptor.ringQ
	id := sk.ID
	level := ct.Level()

	if !ct.Value[id].IsNTT {
		ringQ.NTTLvl(level, ct.Value[id], ct.Value[id])
	}

	e1 := ringQ.NewPoly()
	// decryptor.gaussianSamplerQ.Read(e1) // Partial dec 노이즈 제로
	ringQ.NTTLvl(level, e1, e1)

	ringQ.MulCoeffsMontgomeryLvl(level, ct.Value[id], sk.Value.Q, ct.Value[id])
	ringQ.AddLvl(level, e1, ct.Value[id], ct.Value[id])

	if !ct.Value[id].IsNTT {
		ringQ.InvNTTLvl(level, ct.Value[id], ct.Value[id])
	}

	ringQ.AddLvl(level, ct.Value["0"], ct.Value[id], ct.Value["0"])
	delete(ct.Value, id)
}

// PartialDecrypt partially decrypts the ct with single secretkey sk and update result inplace
func (decryptor *Decryptor) PartialDecryptIP(ct *Ciphertext, sk *SecretKey) {
	ringQ := decryptor.ringQ
	id := sk.ID
	level := ct.Level()

	if !ct.Value[id].IsNTT {
		ringQ.NTTLvl(level, ct.Value[id], ct.Value[id])
	}

	e1 := ringQ.NewPoly()
	decryptor.NFgaussianSamplerQ.Read(e1)
	// fmt.Print(e1)
	ringQ.NTTLvl(level, e1, e1)

	ringQ.MulCoeffsMontgomeryLvl(level, ct.Value[id], sk.Value.Q, ct.Value[id])
	ringQ.AddLvl(level, e1, ct.Value[id], ct.Value[id])

	if !ct.Value[id].IsNTT {
		ringQ.InvNTTLvl(level, ct.Value[id], ct.Value[id])
	}

	// ringQ.AddLvl(level, ct.Value["0"], ct.Value[id], ct.Value["0"])
	// delete(ct.Value, id)
}

// Decrypt decrypts the ciphertext with given secretkey set and write the result in ptOut.
// The level of the output plaintext is min(ciphertext.Level(), plaintext.Level())
// Output domain will match plaintext.Value.IsNTT value.
func (decryptor *Decryptor) Decrypt(ciphertext *Ciphertext, skSet *SecretKeySet, plaintext *rlwe.Plaintext) {
	ringQ := decryptor.ringQ
	level := utils.MinInt(ciphertext.Level(), plaintext.Level())
	plaintext.Value.Coeffs = plaintext.Value.Coeffs[:level+1]

	ctTmp := ciphertext.CopyNew()
	idset := ctTmp.IDSet()
	for _, sk := range skSet.Value {
		if idset.Has(sk.ID) {
			decryptor.PartialDecrypt(ctTmp, sk)
			// fmt.Print(sk.ID, "\n")
		}
	}

	if len(ctTmp.Value) > 1 {
		panic("Cannot Decrypt: there is a missing secretkey")
	}

	ringQ.ReduceLvl(level, ctTmp.Value["0"], plaintext.Value)
}

func (decryptor *Decryptor) DecryptSk(ciphertext *Ciphertext, sk *SecretKey, plaintext *rlwe.Plaintext) {
	ringQ := decryptor.ringQ
	level := utils.MinInt(ciphertext.Level(), plaintext.Level())
	plaintext.Value.Coeffs = plaintext.Value.Coeffs[:level+1]

	ctTmp := ciphertext.CopyNew()
	// idset := ctTmp.IDSet()
	// idset.Has(sk.ID)
	decryptor.PartialDecrypt(ctTmp, sk)
	// fmt.Print(sk.ID, "\n")

	ringQ.ReduceLvl(level, ctTmp.Value["0"], plaintext.Value)
}
