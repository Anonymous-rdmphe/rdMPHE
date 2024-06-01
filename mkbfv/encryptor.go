package mkbfv

import (
	"mk-lattigo/mkrlwe"

	"github.com/ldsec/lattigo/v2/bfv"
	"github.com/ldsec/lattigo/v2/rlwe"
)

type Encryptor struct {
	*mkrlwe.Encryptor
	params   Parameters
	encoder  bfv.Encoder
	ptxtPool *bfv.Plaintext
}

// NewEncryptor instantiates a new Encryptor for the BFV scheme.
func NewEncryptor(params Parameters) *Encryptor {
	bfvParams, _ := bfv.NewParameters(params.Parameters.Parameters, params.T())

	ret := new(Encryptor)
	ret.Encryptor = mkrlwe.NewEncryptor(params.Parameters)
	ret.encoder = bfv.NewEncoder(bfvParams)
	ret.params = params
	ret.ptxtPool = bfv.NewPlaintext(bfvParams)

	return ret
}

// Encrypt encrypts the input plaintext and write the result on ctOut.
// The encryption algorithm depends on how the receiver encryptor was initialized (see
// NewEncryptor and NewFastEncryptor).
func (enc *Encryptor) EncryptPtxt(plaintext *bfv.Plaintext, pk *mkrlwe.PublicKey, ctOut *Ciphertext) {
	enc.Encryptor.Encrypt(&rlwe.Plaintext{Value: plaintext.Value}, pk, &mkrlwe.Ciphertext{Value: ctOut.Value})
}

func (enc *Encryptor) EncryptSkPtxt(plaintext *bfv.Plaintext, sk *mkrlwe.SecretKey, ctOut *Ciphertext) {
	enc.Encryptor.EncryptSk(&rlwe.Plaintext{Value: plaintext.Value}, sk, &mkrlwe.Ciphertext{Value: ctOut.Value})
}

// EncryptMsg encode message and then encrypts the input plaintext and write the result on ctOut. The encryption
// algorithm depends on how the receiver encryptor was initialized (see NewEncryptor
// and NewFastEncryptor).
// The level of the output ciphertext is min(plaintext.Level(), ciphertext.Level()).
func (enc *Encryptor) EncryptMsg(msg *Message, pk *mkrlwe.PublicKey, ctOut *Ciphertext) {
	enc.encoder.EncodeInt(msg.Value, enc.ptxtPool)
	enc.EncryptPtxt(enc.ptxtPool, pk, ctOut)
}

func (enc *Encryptor) EncryptSkMsg(msg *Message, sk *mkrlwe.SecretKey, ctOut *Ciphertext) {
	enc.encoder.EncodeInt(msg.Value, enc.ptxtPool)
	enc.EncryptSkPtxt(enc.ptxtPool, sk, ctOut)
}

// EncryptMsg encode message and then encrypts the input plaintext and write the result on ctOut. The encryption
// algorithm depends on how the receiver encryptor was initialized (see NewEncryptor
// and NewFastEncryptor).
// The level of the output ciphertext is min(plaintext.Level(), ciphertext.Level()).
func (enc *Encryptor) EncryptMsgNew(msg *Message, pk *mkrlwe.PublicKey) (ctOut *Ciphertext) {
	idset := mkrlwe.NewIDSet()
	idset.Add(pk.ID)
	ctOut = NewCiphertext(enc.params, idset)
	enc.EncryptMsg(msg, pk, ctOut)

	/*
		for id := range ctOut.Value {
			enc.params.RingQ().NTT(ctOut.Value[id], ctOut.Value[id])
			ctOut.Value[id].IsNTT = true
		}
	*/

	return
}

func (enc *Encryptor) EncryptSkMsgNew(msg *Message, sk *mkrlwe.SecretKey) (ctOut *Ciphertext) {
	idset := mkrlwe.NewIDSet()
	idset.Add(sk.ID)
	ctOut = NewCiphertext(enc.params, idset)
	enc.EncryptSkMsg(msg, sk, ctOut)

	/*
		for id := range ctOut.Value {
			enc.params.RingQ().NTT(ctOut.Value[id], ctOut.Value[id])
			ctOut.Value[id].IsNTT = true
		}
	*/

	return
}
