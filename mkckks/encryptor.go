package mkckks

import (
	"mk-lattigo/mkrlwe"

	"github.com/ldsec/lattigo/v2/ckks"
	"github.com/ldsec/lattigo/v2/rlwe"
)

type Encryptor struct {
	*mkrlwe.Encryptor
	encoder    ckks.Encoder
	params     Parameters
	ckksParams ckks.Parameters
	ptxtPool   *ckks.Plaintext
}

// NewEncryptor instatiates a new Encryptor for the CKKS scheme. The key argument can
// be either a *rlwe.PublicKey or a *rlwe.SecretKey.
func NewEncryptor(params Parameters) *Encryptor {
	ckksParams, _ := ckks.NewParameters(params.Parameters.Parameters, params.LogSlots(), params.Scale())

	ret := new(Encryptor)
	ret.Encryptor = mkrlwe.NewEncryptor(params.Parameters)
	ret.encoder = ckks.NewEncoder(ckksParams)
	ret.params = params
	ret.ckksParams = ckksParams
	ret.ptxtPool = ckks.NewPlaintext(ckksParams, params.MaxLevel(), params.Scale())
	return ret
}

// Encrypt encrypts the input plaintext and write the result on ctOut. The encryption
// algorithm depends on how the receiver encryptor was initialized (see NewEncryptor
// and NewFastEncryptor).
// The level of the output ciphertext is min(plaintext.Level(), ciphertext.Level()).
func (enc *Encryptor) EncryptPtxt(plaintext *ckks.Plaintext, pk *mkrlwe.PublicKey, ctOut *Ciphertext) {
	enc.Encryptor.Encrypt(&rlwe.Plaintext{Value: plaintext.Value}, pk, &mkrlwe.Ciphertext{Value: ctOut.Value})
	ctOut.Scale = plaintext.Scale
}

func (enc *Encryptor) EncryptSkPtxt(plaintext *ckks.Plaintext, sk *mkrlwe.SecretKey, ctOut *Ciphertext) {
	enc.Encryptor.EncryptSk(&rlwe.Plaintext{Value: plaintext.Value}, sk, &mkrlwe.Ciphertext{Value: ctOut.Value})
	ctOut.Scale = plaintext.Scale
}

// EncryptMsg encode message and then encrypts the input plaintext and write the result on ctOut. The encryption
// algorithm depends on how the receiver encryptor was initialized (see NewEncryptor
// and NewFastEncryptor).
// The level of the output ciphertext is min(plaintext.Level(), ciphertext.Level()).
func (enc *Encryptor) EncryptMsg(msg *Message, pk *mkrlwe.PublicKey, ctOut *Ciphertext) {
	enc.encoder.Encode(enc.ptxtPool, msg.Value, enc.params.LogSlots())
	enc.EncryptPtxt(enc.ptxtPool, pk, ctOut)
}

func (enc *Encryptor) EncryptSkMsg(msg *Message, sk *mkrlwe.SecretKey, ctOut *Ciphertext) {
	enc.encoder.Encode(enc.ptxtPool, msg.Value, enc.params.LogSlots())
	enc.EncryptSkPtxt(enc.ptxtPool, sk, ctOut)
}

// EncryptMsg encode message and then encrypts the input plaintext and write the result on ctOut. The encryption
// algorithm depends on how the receiver encryptor was initialized (see NewEncryptor
// and NewFastEncryptor).
// The level of the output ciphertext is min(plaintext.Level(), ciphertext.Level()).
func (enc *Encryptor) EncryptMsgNew(msg *Message, pk *mkrlwe.PublicKey) (ctOut *Ciphertext) {
	idset := mkrlwe.NewIDSet()
	idset.Add(pk.ID)
	ctOut = NewCiphertext(enc.params, idset, enc.params.MaxLevel(), enc.params.Scale())
	enc.EncryptMsg(msg, pk, ctOut)

	return
}

func (enc *Encryptor) EncryptSkMsgNew(msg *Message, sk *mkrlwe.SecretKey) (ctOut *Ciphertext) {
	idset := mkrlwe.NewIDSet()
	idset.Add(sk.ID)
	ctOut = NewCiphertext(enc.params, idset, enc.params.MaxLevel(), enc.params.Scale())
	enc.EncryptSkMsg(msg, sk, ctOut)

	return
}

func (enc *Encryptor) EncodeMsgNew(msg *Message) (ptxtOut *ckks.Plaintext) {
	ptxtOut = ckks.NewPlaintext(enc.ckksParams, enc.params.MaxLevel(), enc.params.Scale())
	enc.encoder.Encode(ptxtOut, msg.Value, enc.params.LogSlots())
	return
}

func (enc *Encryptor) EncryptMsgNewScale(msg *Message, pk *mkrlwe.PublicKey, scale float64) (ctOut *Ciphertext) {
	idset := mkrlwe.NewIDSet()
	idset.Add(pk.ID)
	ctOut = NewCiphertext(enc.params, idset, enc.params.MaxLevel(), scale)
	enc.EncryptMsg(msg, pk, ctOut)

	return
}

func (enc *Encryptor) EncodeMsgNewScale(msg *Message, scale float64) (ptxtOut *ckks.Plaintext) {
	ptxtOut = ckks.NewPlaintext(enc.ckksParams, enc.params.MaxLevel(), scale)
	enc.encoder.Encode(ptxtOut, msg.Value, enc.params.LogSlots())
	return
}
