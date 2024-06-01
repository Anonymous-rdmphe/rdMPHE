package mkckks

import (
	"flag"
	"fmt"
	"strconv"
	"testing"
	"time"

	"mk-lattigo/mkrlwe"

	"github.com/ldsec/lattigo/v2/ckks"
	"github.com/ldsec/lattigo/v2/ring"
	"github.com/ldsec/lattigo/v2/rlwe"
	"github.com/ldsec/lattigo/v2/utils"

	"math"
	"math/big"
	"math/cmplx"

	"github.com/stretchr/testify/require"
	// "github.com/xuri/excelize/v2"
)

type KeyGenerator struct {
	params           Parameters
	poolQ            *ring.Poly
	poolQP           rlwe.PolyQP
	gaussianSamplerQ *ring.GaussianSampler
	uniformSamplerQ  *ring.UniformSampler
	uniformSamplerP  *ring.UniformSampler
}

// Returns the ceil(log2) of the sum of the absolute value of all the coefficients
func log2OfInnerSum(level int, ringQ *ring.Ring, poly *ring.Poly) (logSum float64) {
	sumRNS := make([]uint64, level+1)

	for j := 0; j < ringQ.N; j++ {

		for i := 0; i < level+1; i++ {
			coeffs := poly.Coeffs[i]
			sumRNS[i] = coeffs[j]
		}

		var qi uint64
		var crtReconstruction *big.Int

		sumBigInt := ring.NewUint(0)
		QiB := new(big.Int)
		tmp := new(big.Int)
		modulusBigint := ring.NewInt(1)

		for i := 0; i < level+1; i++ {

			qi = ringQ.Modulus[i]
			QiB.SetUint64(qi)

			modulusBigint.Mul(modulusBigint, QiB)

			crtReconstruction = new(big.Int)
			crtReconstruction.Quo(ringQ.ModulusBigint, QiB)
			tmp.ModInverse(crtReconstruction, QiB)
			tmp.Mod(tmp, QiB)
			crtReconstruction.Mul(crtReconstruction, tmp)

			sumBigInt.Add(sumBigInt, tmp.Mul(ring.NewUint(sumRNS[i]), crtReconstruction))
		}

		sumBigInt.Mod(sumBigInt, modulusBigint)
		sumBigInt.Abs(sumBigInt)
		logSum1 := sumBigInt.BitLen()

		sumBigInt.Sub(sumBigInt, modulusBigint)
		sumBigInt.Abs(sumBigInt)
		logSum2 := sumBigInt.BitLen()

		if logSum1 < logSum2 {
			logSum += float64(logSum1) / float64(ringQ.N)
		} else {
			logSum += float64(logSum2) / float64(ringQ.N)
		}
	}

	return
}

var maxGroups = flag.Int("n", 32, "maximum number of groups")

func GetTestName(params Parameters, opname string) string {
	return fmt.Sprintf("%slogN=%d/LogSlots=%d/logQP=%d/levels=%d/",
		opname,
		params.LogN(),
		params.LogSlots(),
		params.LogQP(),
		params.MaxLevel()+1)
}

type testParams struct {
	params     Parameters
	ringQ      *ring.Ring
	ringP      *ring.Ring
	prng       utils.PRNG
	kgen       *mkrlwe.KeyGenerator
	skSet      *mkrlwe.SecretKeySet
	pkSet      *mkrlwe.PublicKeySet
	rlkSet     *mkrlwe.RelinearizationKeySet
	swkSet     [32]*mkrlwe.SWKSet
	swkheadSet [32]*mkrlwe.SWKSet
	rtkSet     *mkrlwe.RotationKeySet
	cjkSet     *mkrlwe.ConjugationKeySet

	encryptor *Encryptor
	decryptor *Decryptor
	evaluator *Evaluator
	idset     *mkrlwe.IDSet
}

var (
	// PN12QP109 is a default parameter set for logN=12 and logQP=109
	PN12QP109 = ckks.ParametersLiteral{
		LogN:     12,
		LogSlots: 11,
		Q: []uint64{0x200000e001, // 37 + 32
			0x100006001},
		P:     []uint64{0x3ffffea001}, // 38
		Scale: 1 << 32,
		Sigma: rlwe.DefaultSigma,
	}

	PN15QP880 = ckks.ParametersLiteral{
		LogN:     15,
		LogSlots: 14,
		//55 + 13x54
		Q: []uint64{
			0x7fffffffba0001,
			0x3fffffffd60001, 0x3fffffffca0001,
			0x3fffffff6d0001, 0x3fffffff5d0001,
			0x3fffffff550001, 0x3fffffff390001,
			0x3fffffff360001, 0x3fffffff2a0001,
			0x3fffffff000001, 0x3ffffffefa0001,
			0x3ffffffef40001, 0x3ffffffed70001,
			0x3ffffffed30001,
		},
		P: []uint64{

			// 30, 45, 60 x 2

			// 0x3ffc0001, 0x3fde0001,

			//0x1fffffc20001, 0x1fffff980001,

			0xffffffffffc0001, 0xfffffffff840001,
		},
		Scale: 1 << 54,
		Sigma: rlwe.DefaultSigma,
	}

	PN14QP439 = ckks.ParametersLiteral{
		LogN:     14,
		LogSlots: 13,
		Q: []uint64{
			// 53 + 5x52
			0x1fffffffd80001,
			0xffffffff00001, 0xfffffffe40001,
			0xfffffffe20001, 0xfffffffbe0001,
			0xfffffffa60001,
		},
		P: []uint64{
			// 30, 45, 60 x 2

			//0x3ffc0001, 0x3fde0001,

			//0x1fffffc20001, 0x1fffff980001,

			0xffffffffffc0001, 0xfffffffff840001,
		},
		Scale: 1 << 52,
		Sigma: rlwe.DefaultSigma,
	}
)

func Test_CKKS_rdMPHE(t *testing.T) {
	defaultParams := []ckks.ParametersLiteral{PN14QP439, PN15QP880}
	for _, defaultParam := range defaultParams {
		fmt.Print("========Paramset=========", "\n")
		for _, numParties := range []int{1, 3, 7, 15, 31} {

			// number of parties in each group
			JoiningParties := 1
			numCtxt := 1

			fmt.Print("================= CKKS_rdMPHE ", numParties+JoiningParties, "===================", "\n", "\n", "\n")

			KGstart := time.Now()
			ckksParams, err := ckks.NewParametersFromLiteral(defaultParam)

			if err != nil {
				panic(err)
			}

			if ckksParams.PCount() < 2 {
				continue
			}

			params := NewParameters(ckksParams)
			groupList := make([]string, *maxGroups)
			idset := mkrlwe.NewIDSet()

			for i := range groupList {
				groupList[i] = "group" + strconv.Itoa(i)
				idset.Add(groupList[i])
			}

			var testContext2 *testParams

			sk := make([]*mkrlwe.SecretKey, numParties)
			pk := make([]*mkrlwe.PublicKey, numParties)
			rlk := make([]*mkrlwe.RelinearizationKey, numParties)
			cjk := make([]*mkrlwe.ConjugationKey, numParties)
			rtks := make([]map[uint]*mkrlwe.RotationKey, numParties)
			var gsk *mkrlwe.SecretKey
			var gsk2 *mkrlwe.SecretKey
			var gpk *mkrlwe.PublicKey
			var gpk2 *mkrlwe.PublicKey
			var grlk *mkrlwe.RelinearizationKey
			var grlk2 *mkrlwe.RelinearizationKey
			var gcjk *mkrlwe.ConjugationKey
			var gcjk2 *mkrlwe.ConjugationKey
			var grtk *mkrlwe.RotationKey
			var grtk2 *mkrlwe.RotationKey

			swk := make([]*mkrlwe.SWK, numParties+JoiningParties)
			swkhead := make([]*mkrlwe.SWK, numParties+JoiningParties)
			swk2 := make([]*mkrlwe.SWK, numParties+JoiningParties)
			swkhead2 := make([]*mkrlwe.SWK, numParties+JoiningParties)

			testContext2, err, gsk, gpk, grlk, gcjk, grtk, sk, pk, rlk, cjk, rtks = genTestParams(params, gsk, gpk, grlk, gcjk, grtk, sk, pk, rlk, cjk, rtks, idset, numParties)

			swksum := mkrlwe.NewSWK(testContext2.params.Parameters, "group0")
			swkheadsum := mkrlwe.NewSWK(testContext2.params.Parameters, "group0")
			testContext2, err, swk, swkhead, swksum, swkheadsum = MPgenSWK(testContext2, gsk, gpk, sk, pk, rlk, cjk, swk, swkhead, swksum, swkheadsum, rtks, idset, numParties)
			KGend := time.Since(KGstart)
			fmt.Print("Key Generation time = ", KGend, "\n")

			msgList := make([]*Message, numCtxt)
			ctxtList := make([]*Ciphertext, numCtxt)
			msg := msgList[0]
			ctxt := ctxtList[0]
			ctsk := ctxtList[0]

			msg, ctxt, ctsk = testKS(testContext2, groupList, gsk, gpk, sk, pk, swk, swkhead, t)

			_ = msg
			_ = ctsk

			for i := 0; i < numCtxt; i++ {
				ctxtList[i] = ctxt.CopyNew()
			}

			Updatestart := time.Now()
			jk := mkrlwe.NewSWK(testContext2.params.Parameters, "group0")
			jkhead := mkrlwe.NewSWK(testContext2.params.Parameters, "group0")
			uaux := mkrlwe.NewSWK(testContext2.params.Parameters, "group0")
			uauxhead := mkrlwe.NewSWK(testContext2.params.Parameters, "group0")

			// Joining
			testContext2, err, gsk2, gpk2, grlk2, gcjk2, grtk2, sk, pk, rlk, cjk, swk2, swkhead2, swksum, swkheadsum, rtks, jk, jkhead, uaux, uauxhead, ctxtList = testJoinPartyMP(testContext2, gsk, gpk, grlk, gcjk, grtk, sk, pk, rlk, cjk, swk, swkhead, swksum, swkheadsum, rtks, jk, jkhead, uaux, uauxhead, idset, numParties, JoiningParties, ctxtList, t)
			Updateend := time.Since(Updatestart)
			fmt.Print("Extend (key+ctxt) time = ", Updateend, "\n")
			// msg, ctOut, ctsk = testKS(testContext2, groupList, gsk2, gpk2, sk, pk, swk, swkhead, t)
			// ctsk2 := ctsk.CopyNew()

			testKSAfterJoin(testContext2, groupList, msg, ctxt, ctsk, gsk, gsk2, gpk, gpk2, sk, pk, swk2, swkhead2, jk, jkhead, uaux, uauxhead, ctxtList, t)

			_, _, _, _, _, _, _ = gsk2, gpk2, grlk2, gcjk2, grtk2, swk2, swkhead2

			// Eval tests
			testEvaluatorAdd(testContext2, groupList, t)
			testEvaluatorMul(testContext2, groupList, t)
			testEvaluatorRot(testContext2, groupList, t)
			testEvaluatorConj(testContext2, groupList, t)
		}
	}
}

func Test_MKHE_CKKS(t *testing.T) {
	defaultParams := []ckks.ParametersLiteral{PN14QP439, PN15QP880}
	for _, defaultParam := range defaultParams {
		fmt.Print("========Paramset=========", "\n")
		for _, num := range []int{1, 3, 7, 15, 31} {
			*maxGroups = num
			// number of parties in each group
			numParties := 1 // when this is 1, MKHE.
			JoiningParties := 1

			fmt.Print("================= MKHE_CKKS ", *maxGroups+1, "===================", "\n", "\n", "\n")
			/////////////////////////////////////////////////////////////////////////////////////////////////////
			KGstart := time.Now()
			ckksParams, err := ckks.NewParametersFromLiteral(defaultParam)

			if err != nil {
				panic(err)
			}

			if ckksParams.PCount() < 2 {
				continue
			}

			params := NewParameters(ckksParams)
			groupList := make([]string, *maxGroups)
			idset := mkrlwe.NewIDSet()

			for i := range groupList {
				groupList[i] = "group" + strconv.Itoa(i)
				idset.Add(groupList[i])
			}

			//generate  evaluation keys for each group
			var testContext2 *testParams

			sk := make([]*mkrlwe.SecretKey, numParties)
			pk := make([]*mkrlwe.PublicKey, numParties)
			rlk := make([]*mkrlwe.RelinearizationKey, numParties)
			cjk := make([]*mkrlwe.ConjugationKey, numParties)
			rtks := make([]map[uint]*mkrlwe.RotationKey, numParties)
			var gsk *mkrlwe.SecretKey
			var gsk2 *mkrlwe.SecretKey
			var gpk *mkrlwe.PublicKey
			var gpk2 *mkrlwe.PublicKey
			var grlk *mkrlwe.RelinearizationKey
			var grlk2 *mkrlwe.RelinearizationKey
			var gcjk *mkrlwe.ConjugationKey
			var gcjk2 *mkrlwe.ConjugationKey
			var grtk *mkrlwe.RotationKey
			var grtk2 *mkrlwe.RotationKey

			swk2 := make([]*mkrlwe.SWK, numParties+JoiningParties)
			swkhead2 := make([]*mkrlwe.SWK, numParties+JoiningParties)

			testContext2, err, gsk, gpk, grlk, gcjk, grtk, sk, pk, rlk, cjk, rtks = genTestParams(params, gsk, gpk, grlk, gcjk, grtk, sk, pk, rlk, cjk, rtks, idset, numParties)
			KGend := time.Since(KGstart)
			fmt.Print("Key Generation time = ", KGend, "\n")

			// fmt.Print("skup = ", sk[0].Value.Q.Coeffs[2][3], "\n")
			/////////////////////////////////////////////////////////////////////////////////////////////////////
			// MKHE
			Updatestart := time.Now()
			testContext2, idset, err, sk, pk, rlk, cjk, rtks = testJoinPartyMK(testContext2, sk, pk, rlk, cjk, rtks, idset, groupList, numParties, JoiningParties, t)
			groupListup := make([]string, *maxGroups+1)
			for i := range groupListup {
				groupListup[i] = "group" + strconv.Itoa(i)
				// idset.Add(groupList[i])
			}
			groupList = groupListup
			Updateend := time.Since(Updatestart)
			fmt.Print("Extend (key) Generation time = ", Updateend, "\n")

			_, _, _, _, _, _, _ = gsk2, gpk2, grlk2, gcjk2, grtk2, swk2, swkhead2

			// fmt.Print("skup = ", skup, "\n")
			// fmt.Print("groupList = ", groupList, "\n")

			// Eval tests
			testEvaluatorAdd(testContext2, groupList, t)
			testEvaluatorMul(testContext2, groupList, t)
			testEvaluatorRot(testContext2, groupList, t)
			testEvaluatorConj(testContext2, groupList, t)
		}
	}
}

func genTestParams(defaultParam Parameters,
	gsk *mkrlwe.SecretKey, gpk *mkrlwe.PublicKey, grlk *mkrlwe.RelinearizationKey, gcjk *mkrlwe.ConjugationKey, grtk *mkrlwe.RotationKey, sk []*mkrlwe.SecretKey, pk []*mkrlwe.PublicKey, rlk []*mkrlwe.RelinearizationKey, cjk []*mkrlwe.ConjugationKey, rtks []map[uint]*mkrlwe.RotationKey,
	groupIdSet *mkrlwe.IDSet, numParties int) (testContext *testParams, err error,
	gskup *mkrlwe.SecretKey, gpkup *mkrlwe.PublicKey, grlkup *mkrlwe.RelinearizationKey, gcjkup *mkrlwe.ConjugationKey, grtkup *mkrlwe.RotationKey, skup []*mkrlwe.SecretKey, pkup []*mkrlwe.PublicKey, rlkup []*mkrlwe.RelinearizationKey, cjkup []*mkrlwe.ConjugationKey, rtksup []map[uint]*mkrlwe.RotationKey) {

	testContext = new(testParams)

	testContext.params = defaultParam

	testContext.kgen = NewKeyGenerator(testContext.params)

	testContext.skSet = mkrlwe.NewSecretKeySet()
	testContext.pkSet = mkrlwe.NewPublicKeyKeySet()
	testContext.rlkSet = mkrlwe.NewRelinearizationKeySet(defaultParam.Parameters)
	testContext.rtkSet = mkrlwe.NewRotationKeySet()
	testContext.cjkSet = mkrlwe.NewConjugationKeySet()

	// gen group sk, pk, rlk, rk

	for groupId := range groupIdSet.Value {
		for p := 0; p < numParties; p++ {
			sk[p], pk[p] = testContext.kgen.GenKeyPair(groupId)
			rlk[p] = testContext.kgen.GenRelinearizationKey(sk[p])
			cjk[p] = testContext.kgen.GenConjugationKey(sk[p])
			rtks[p] = testContext.kgen.GenDefaultRotationKeys(sk[p])
		}

		gsk := testContext.kgen.GenGroupSecretKey(sk)
		testContext.skSet.AddSecretKey(gsk)

		gpk := testContext.kgen.GenGroupPublicKey(pk)
		testContext.pkSet.AddPublicKey(gpk)

		grlk := testContext.kgen.GenGroupRelinKey(rlk)
		testContext.rlkSet.AddRelinearizationKey(grlk)

		gcjk := testContext.kgen.GenGroupConjKey(cjk)
		testContext.cjkSet.AddConjugationKey(gcjk)

		for idx, _ := range rtks[0] {
			rtk := make([]*mkrlwe.RotationKey, numParties)
			for p := 0; p < numParties; p++ {
				rtk[p] = rtks[p][idx]
			}
			grtk = testContext.kgen.GenGroupRotKey(rtk)
			testContext.rtkSet.AddRotationKey(grtk)
		}
		gskup = gsk
		gpkup = gpk
		grlkup = grlk
		gcjkup = gcjk
		grtkup = grtk
	}

	testContext.ringQ = defaultParam.RingQ()

	skup = sk
	pkup = pk
	rlkup = rlk
	cjkup = cjk
	rtksup = rtks

	if testContext.prng, err = utils.NewPRNG(); err != nil {
		return nil, err, gskup, gpkup, grlkup, gcjkup, grtkup, skup, pkup, rlkup, cjkup, rtksup
	}

	testContext.encryptor = NewEncryptor(testContext.params)
	testContext.decryptor = NewDecryptor(testContext.params)
	testContext.evaluator = NewEvaluator(testContext.params)

	return testContext, nil, gskup, gpkup, grlkup, gcjkup, grtkup, skup, pkup, rlkup, cjkup, rtksup
}

func newTestVectors(testContext *testParams, id string, a, b complex128) (msg *Message, ciphertext *Ciphertext) {

	params := testContext.params
	logSlots := testContext.params.LogSlots()

	msg = NewMessage(params)

	for i := 0; i < 1<<logSlots; i++ {
		msg.Value[i] = complex(utils.RandFloat64(real(a), real(b)), utils.RandFloat64(imag(a), imag(b)))
	}

	if testContext.encryptor != nil {
		ciphertext = testContext.encryptor.EncryptMsgNew(msg, testContext.pkSet.GetPublicKey(id))
	} else {
		panic("cannot newTestVectors: encryptor is not initialized!")
	}

	return msg, ciphertext
}

func newTestVectorsSk(testContext *testParams, id string, a, b complex128) (msg *Message, ciphertext *Ciphertext) {

	params := testContext.params
	logSlots := testContext.params.LogSlots()

	msg = NewMessage(params)

	for i := 0; i < 1<<logSlots; i++ {
		msg.Value[i] = complex(utils.RandFloat64(real(a), real(b)), utils.RandFloat64(imag(a), imag(b)))
	}

	if testContext.encryptor != nil {
		ciphertext = testContext.encryptor.EncryptSkMsgNew(msg, testContext.skSet.GetSecretKey(id))
	} else {
		panic("cannot newTestVectors: encryptor is not initialized!")
	}

	return msg, ciphertext
}

func testEncAndDec(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	skSet := testContext.skSet
	dec := testContext.decryptor

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i], complex(-1, -1), complex(1, 1))
	}

	t.Run(GetTestName(testContext.params, "MKCKKSEncAndDec: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {

		for i := range userList {
			msgOut := dec.Decrypt(ctList[i], skSet)
			for j := range msgList[i].Value {
				delta := msgList[i].Value[j] - msgOut.Value[j]
				require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
			}
		}
	})

}

// Returns the ceil(log2) of the sum of the absolute value of all the coefficients

func testEvaluatorAdd(testContext *testParams, userList []string, t *testing.T) {

	t.Run(GetTestName(testContext.params, "Evaluator/Add/CtCt/"), func(t *testing.T) {
		params := testContext.params
		msg3 := NewMessage(params)

		numUsers := len(userList)
		msgList := make([]*Message, numUsers)
		ctList := make([]*Ciphertext, numUsers)

		eval := testContext.evaluator

		for i := range userList {
			msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
				complex(0.1/float64(numUsers), 1.0/float64(numUsers)),
				complex(0.1/float64(numUsers), 1.0/float64(numUsers)))
		}

		ct := ctList[0]
		msg := msgList[0]

		for i := range userList {
			ct = eval.AddNew(ct, ctList[i])

			for j := range msg.Value {
				msg.Value[j] += msgList[i].Value[j]
			}
		}

		for i := range msg3.Value {
			msg3.Value[i] = msg.Value[i] + msg.Value[i]
		}

		Addstart := time.Now()
		ct3 := testContext.evaluator.AddNew(ct, ct)
		Addend := time.Since(Addstart)
		fmt.Print("Add time = ", Addend, "\n")

		msg1Out := testContext.decryptor.Decrypt(ct, testContext.skSet)
		msg2Out := testContext.decryptor.Decrypt(ct, testContext.skSet)
		msg3Out := testContext.decryptor.Decrypt(ct3, testContext.skSet)

		for i := range msg1Out.Value {
			delta := msg.Value[i] - msg1Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg2Out.Value {
			delta := msg.Value[i] - msg2Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg3Out.Value {
			delta := msg3.Value[i] - msg3Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
		}
		require.Equal(t, 0, 0)
	})

}

func testKS(testContext *testParams, userList []string, gsk *mkrlwe.SecretKey, gpk *mkrlwe.PublicKey, sk []*mkrlwe.SecretKey, pk []*mkrlwe.PublicKey, swk []*mkrlwe.SWK, swkhead []*mkrlwe.SWK, t *testing.T) (msg *Message, ctxt *Ciphertext, ctsk *Ciphertext) {

	params := testContext.params
	eval := testContext.evaluator
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1

	numUsers := len(sk)
	msgListpk := make([]*Message, numUsers)
	ctListpk := make([]*Ciphertext, numUsers)
	msgListsk := make([]*Message, numUsers)
	ctListsk := make([]*Ciphertext, numUsers)

	for i := range userList {
		msgListpk[i], ctListpk[i] = newTestVectors(testContext, userList[i],
			complex(0.1, 0.1), complex(0.1, 0.1))
		msgListsk[i], ctListsk[i] = newTestVectorsSk(testContext, userList[i],
			complex(0.1, 0.1), complex(0.1, 0.1))
	}

	ctOut := ctListsk[0]
	msg = msgListsk[0]
	msg3Out := msgListsk[0]
	fmt.Print("Original Message = ", msg.Value[0], "\n")
	_ = msg

	// skzero := sk[0].CopyNew()
	skOut := sk[0].CopyNew()
	for i := range sk {
		if i != 0 {
			params.RingQP().AddLvl(levelQ, levelP, skOut.Value, sk[i].Value, skOut.Value)
		}
	}

	ctpk := testContext.encryptor.EncryptMsgNew(msg, gpk) // testContext.pkSet.GetPublicKey("group0"))
	msg1Out := testContext.decryptor.DecryptSk(ctpk, skOut)
	// fmt.Print("pkEnc TEST = ", msg1Out.Value[0], "\n")
	_ = msg1Out

	ctsk = testContext.encryptor.EncryptSkMsgNew(msg, sk[0]) //testContext.skSet.GetSecretKey("group0"))
	ctskorigin := ctsk.CopyNew()
	msg2Out := testContext.decryptor.DecryptSk(ctsk, sk[0])
	// fmt.Print("skEnc TEST = ", msg2Out.Value[0], "\n")
	_ = msg2Out
	eval.ksw.KS(ctsk.Ciphertext, swk[0], swkhead[0], ctOut.Ciphertext)

	// Partial Decrypt
	ptxt := testContext.decryptor.ptxtPool
	ctdecList := make([]*Ciphertext, numUsers)
	level := utils.MinInt(ctOut.Level(), ptxt.Plaintext.Level())
	ptxt.Plaintext.Value.Coeffs = ptxt.Plaintext.Value.Coeffs[:level+1]

	for p := range sk {
		ctdecList[p] = ctOut.CopyNew()
	}

	for p := range sk {
		testContext.decryptor.PartialDecryptIP(ctdecList[p], sk[p])
	}
	for p := range sk {
		if p != 0 {
			testContext.ringQ.AddLvl(level, ctdecList[p].Value["group0"], ctdecList[0].Value["group0"], ctdecList[0].Value["group0"])
		}
	}

	testContext.ringQ.AddLvl(level, ctdecList[0].Value["0"], ctdecList[0].Value["group0"], ctdecList[0].Value["0"])
	testContext.ringQ.ReduceLvl(level, ctdecList[0].Value["0"], ptxt.Plaintext.Value)
	testContext.decryptor.ptxtPool.Scale = ctdecList[0].Scale
	msg3Out.Value = testContext.decryptor.encoder.Decode(ptxt, testContext.decryptor.params.logSlots)

	fmt.Print("After Switch + Partial Dec = ", msg3Out.Value[0], "\n")

	for i := range msg.Value {
		delta := msg.Value[i] - msg3Out.Value[i]
		require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
	}
	require.Equal(t, 0, 0)
	ctsk = ctskorigin

	return msg, ctOut, ctsk
}

func testKSAfterJoin(testContext *testParams, userList []string, msg *Message, ctxt *Ciphertext, ctsk *Ciphertext, gsk *mkrlwe.SecretKey, gsk2 *mkrlwe.SecretKey, gpk *mkrlwe.PublicKey, gpk2 *mkrlwe.PublicKey, sk []*mkrlwe.SecretKey, pk []*mkrlwe.PublicKey, swk []*mkrlwe.SWK, swkhead []*mkrlwe.SWK, jk *mkrlwe.SWK, jkhead *mkrlwe.SWK, uaux *mkrlwe.SWK, uauxhead *mkrlwe.SWK, ctxtList []*Ciphertext, t *testing.T) {

	// params := testContext.params
	eval := testContext.evaluator
	// numUsers := len(sk)

	msg2Out := testContext.decryptor.DecryptSk(ctxt, gsk)
	// fmt.Print("Dec TEST = ", msg2Out.Value[0], "\n")
	_ = msg2Out

	// If generate jk
	ctOut := eval.KSNew(ctxt, jk, jkhead)
	msgOut := testContext.decryptor.DecryptSk(ctOut, gsk2)
	fmt.Print("After Switch + Extend = ", msgOut.Value[0], "\n")

	ctOut2 := eval.KSNew(ctsk, swk[0], swkhead[0])
	msg3Out := testContext.decryptor.DecryptSk(ctOut2, gsk2)
	// fmt.Print("Test updated swk_i = ", msg3Out.Value[0], "\n")
	_ = msg3Out

	msg11Out := testContext.decryptor.DecryptSk(ctxtList[0], gsk2)
	// fmt.Print("Test updated (Join) ctxt = ", msg11Out.Value[0], "\n")
	_ = msg11Out

	require.Equal(t, 0, 0)
}

func testEvaluatorMul(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)
	rlkSet := testContext.rlkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)))
	}
	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])
		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	for j := range msg.Value {
		msg.Value[j] *= msg.Value[j]
	}

	ptxt := testContext.decryptor.DecryptToPtxt(ct, testContext.skSet)
	ptxt2 := testContext.decryptor.DecryptToPtxt(ct, testContext.skSet)

	testContext.ringQ.NTT(ptxt, ptxt)
	testContext.ringQ.NTT(ptxt2, ptxt2)
	testContext.ringQ.MForm(ptxt2, ptxt2)
	testContext.ringQ.MulCoeffsMontgomery(ptxt, ptxt2, ptxt)
	testContext.ringQ.InvNTT(ptxt, ptxt)
	testContext.ringQ.DivRoundByLastModulusLvl(ptxt.Level(), ptxt, ptxt)
	ptxt.Coeffs = ptxt.Coeffs[:ptxt.Level()]
	//

	t.Run(GetTestName(testContext.params, "MKMulAndRelin: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ctMulstart := time.Now()
		ctRes := eval.MulRelinNew(ct, ct, rlkSet)
		ctMulend := time.Since(ctMulstart)
		fmt.Print("Mult time = ", ctMulend, "\n")

		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)
		ptxtRes := testContext.decryptor.DecryptToPtxt(ctRes, testContext.skSet)

		testContext.ringQ.Sub(ptxtRes, ptxt, ptxtRes)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			// fmt.Print(msgRes.Value[i], msg.Value[i], "\n")
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(imag(delta))))
		}

		require.Equal(t, 0, 0)
		ctrrr := eval.MulRelinNew(ct, ct, rlkSet)
		require.Equal(t, ctrrr, ctrrr)
	})
}

func testEvaluatorRescale(testContext *testParams, t *testing.T) {

	t.Run(GetTestName(testContext.params, "Evaluator/Rescale/Single/"), func(t *testing.T) {
		params := testContext.params
		msg1, ct1 := newTestVectors(testContext, "user1", complex(-1, -1), complex(1, 1))
		msg2, ct2 := newTestVectors(testContext, "user2", complex(-1, -1), complex(1, 1))
		msg3 := NewMessage(params)

		constant := testContext.ringQ.Modulus[ct1.Level()]

		for i := range msg3.Value {
			msg3.Value[i] = msg1.Value[i] + msg2.Value[i]
		}

		ct3 := testContext.evaluator.AddNew(ct1, ct2)

		testContext.evaluator.MultByConst(ct3, constant, ct3)
		ct3.Scale *= float64(constant)
		testContext.evaluator.Rescale(ct3, params.Scale(), ct3)

		msg1Out := testContext.decryptor.Decrypt(ct1, testContext.skSet)
		msg2Out := testContext.decryptor.Decrypt(ct2, testContext.skSet)
		msg3Out := testContext.decryptor.Decrypt(ct3, testContext.skSet)

		for i := range msg1Out.Value {
			delta := msg1.Value[i] - msg1Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg2Out.Value {
			delta := msg2.Value[i] - msg2Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg3Out.Value {
			delta := msg3.Value[i] - msg3Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
		}
	})

}

func testEvaluatorRot(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	rtkSet := testContext.rtkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]
	rot := int(1)

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	t.Run(GetTestName(testContext.params, "MKRotate: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		// eval.DropLevel(ct, 1)
		Rotstart := time.Now()
		ctRes := eval.RotateNew(ct, rot, rtkSet)
		Rotend := time.Since(Rotstart)
		fmt.Print("Rot time = ", Rotend, "\n")

		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := range msgRes.Value {
			var delta complex128
			if rot > 0 {
				delta = msgRes.Value[i] - msg.Value[(i+rot)%len(msg.Value)]
			} else {
				delta = msg.Value[i] - msgRes.Value[(i-rot)%len(msg.Value)]
			}
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(imag(delta))))
		}
	})

}

func testEvaluatorConj(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	cjkSet := testContext.cjkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	for j := range msg.Value {
		msg.Value[j] = cmplx.Conj(msg.Value[j])
	}

	t.Run(GetTestName(testContext.params, "MKConjugate: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		Conjstart := time.Now()
		ctRes := eval.ConjugateNew(ct, cjkSet)

		Conjend := time.Since(Conjstart)
		fmt.Print("Conj time = ", Conjend, "\n")

		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+20, math.Log2(math.Abs(imag(delta))))
		}
	})

}

func testEvaluatorMulPtxt(testContext *testParams, userList []string, t *testing.T) {

	// params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.1/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.1/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	pt := testContext.encryptor.EncodeMsgNew(msg)

	for j := range msg.Value {
		msg.Value[j] *= msg.Value[j]
	}

	t.Run(GetTestName(testContext.params, "MKMulPtxt: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ptMulstart := time.Now()

		ctRes := eval.MulPtxtNew(ct, pt)
		ptMulend := time.Since(ptMulstart)
		fmt.Print(ptMulend, "\n")

		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		// for i := range msgRes.Value {
		// 	delta := msgRes.Value[i] - msg.Value[i]
		// 	require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots()), math.Log2(math.Abs(real(delta))))
		// 	require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots()), math.Log2(math.Abs(imag(delta))))
		// }
		fmt.Print(msgRes.Value[0], msg.Value[0], "\n")
	})
}

func MPgenSWK(testContext *testParams,
	gsk *mkrlwe.SecretKey, gpk *mkrlwe.PublicKey, sk []*mkrlwe.SecretKey, pk []*mkrlwe.PublicKey, rlk []*mkrlwe.RelinearizationKey, cjk []*mkrlwe.ConjugationKey, swk []*mkrlwe.SWK, swkhead []*mkrlwe.SWK, swksum *mkrlwe.SWK, swkheadsum *mkrlwe.SWK, rtks []map[uint]*mkrlwe.RotationKey,
	groupIdSet *mkrlwe.IDSet,
	numParties int) (testContext2 *testParams, err error, swkup []*mkrlwe.SWK, swkheadup []*mkrlwe.SWK, swksumup *mkrlwe.SWK, swkheadsumup *mkrlwe.SWK) {

	params := testContext.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)

	testContext2 = testContext

	// swksum := mkrlwe.NewSWK(testContext2.params.Parameters, "group0")
	// swkheadsum := mkrlwe.NewSWK(testContext2.params.Parameters, "group0")

	for p := 0; p < numParties; p++ { //for each group...
		testContext2.swkSet[p] = mkrlwe.NewSWKSet()
		testContext2.swkheadSet[p] = mkrlwe.NewSWKSet()
	}

	for p := 0; p < numParties; p++ { //for each group...
		// fmt.Print("sk = ", sk[p], "gpk = ", gpk, "\n")
		swk[p], swkhead[p] = testContext.kgen.GenSWK(sk[p], gpk) // testContext.pkSet.GetPublicKey("group0"))
		// swk[p], swkhead[p] = testContext.kgen.GenSWKTest(sk[p], gsk) //testContext.skSet.GetSecretKey("group0"))

		testContext2.swkSet[p].AddSWK(swk[p])
		testContext2.swkheadSet[p].AddSWK(swkhead[p])
		// fmt.Print(sk[p], "\n")
	}

	for i := 0; i < beta; i++ {
		swksum.Value.Value[i].Q.Copy(swk[0].Value.Value[i].Q)
		swksum.Value.Value[i].P.Copy(swk[0].Value.Value[i].P)
		swkheadsum.Value.Value[i].Q.Copy(swkhead[0].Value.Value[i].Q)
		swkheadsum.Value.Value[i].P.Copy(swkhead[0].Value.Value[i].P)
	}
	for p := 1; p < numParties; p++ {
		for i := 0; i < beta; i++ {
			params.RingQP().AddLvl(levelQ, levelP, swksum.Value.Value[i], swk[p].Value.Value[i], swksum.Value.Value[i])
			params.RingQP().AddLvl(levelQ, levelP, swkheadsum.Value.Value[i], swkhead[p].Value.Value[i], swkheadsum.Value.Value[i])
		}
	}

	// skOut := sk[0]
	// for i := 1; i < 5; i++ {
	// 	params.RingQP().AddLvl(levelQ, levelP, skOut.Value, sk[i].Value, skOut.Value)
	// }

	swkup = swk
	swkheadup = swkhead
	swksumup = swksum
	swkheadsumup = swkheadsum

	if testContext2.prng, err = utils.NewPRNG(); err != nil {
		return nil, err, swkup, swkheadup, swksumup, swkheadsumup
	}

	return testContext2, nil, swkup, swkheadup, swksumup, swkheadsumup
}

/////////////////////////////////////////////////////// Update Party ///////////////////////////////////////////////////////////

func testJoinPartyMP(testContext *testParams,
	gsk *mkrlwe.SecretKey, gpk *mkrlwe.PublicKey, grlk *mkrlwe.RelinearizationKey, gcjk *mkrlwe.ConjugationKey, grtk *mkrlwe.RotationKey, sk []*mkrlwe.SecretKey, pk []*mkrlwe.PublicKey, rlk []*mkrlwe.RelinearizationKey, cjk []*mkrlwe.ConjugationKey, swk []*mkrlwe.SWK, swkhead []*mkrlwe.SWK, swksum *mkrlwe.SWK, swkheadsum *mkrlwe.SWK, rtks []map[uint]*mkrlwe.RotationKey, jk *mkrlwe.SWK, jkhead *mkrlwe.SWK, uaux *mkrlwe.SWK, uauxhead *mkrlwe.SWK,
	groupIdSet *mkrlwe.IDSet, numParties int, JoiningParties int, ctxtList []*Ciphertext, t *testing.T) (testContext2 *testParams, err error, gskup *mkrlwe.SecretKey, gpkup *mkrlwe.PublicKey, grlkup *mkrlwe.RelinearizationKey, gcjkup *mkrlwe.ConjugationKey, grtkup *mkrlwe.RotationKey, skup []*mkrlwe.SecretKey, pkup []*mkrlwe.PublicKey, rlkup []*mkrlwe.RelinearizationKey, cjkup []*mkrlwe.ConjugationKey, swkup []*mkrlwe.SWK, swkheadup []*mkrlwe.SWK, swksumup *mkrlwe.SWK, swkheadsumup *mkrlwe.SWK, rtksup []map[uint]*mkrlwe.RotationKey, jkup *mkrlwe.SWK, jkheadup *mkrlwe.SWK, uauxup *mkrlwe.SWK, uauxheadup *mkrlwe.SWK, ctxtListup []*Ciphertext) {
	testContext2 = testContext

	params := testContext.params
	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	beta := params.Beta(levelQ)
	ringQP := params.RingQP()

	testContext2.skSet = mkrlwe.NewSecretKeySet()
	testContext2.pkSet = mkrlwe.NewPublicKeyKeySet()
	testContext2.rlkSet = mkrlwe.NewRelinearizationKeySet(testContext.params.Parameters)
	testContext2.rtkSet = mkrlwe.NewRotationKeySet()
	testContext2.cjkSet = mkrlwe.NewConjugationKeySet()

	skup = make([]*mkrlwe.SecretKey, numParties+JoiningParties)
	pkup = make([]*mkrlwe.PublicKey, numParties+JoiningParties)
	rlkup = make([]*mkrlwe.RelinearizationKey, numParties+JoiningParties)
	cjkup = make([]*mkrlwe.ConjugationKey, numParties+JoiningParties)
	swkup = make([]*mkrlwe.SWK, numParties+JoiningParties)
	swkheadup = make([]*mkrlwe.SWK, numParties+JoiningParties)
	rtksup = make([]map[uint]*mkrlwe.RotationKey, numParties+JoiningParties)

	Update_KG_start := time.Now()

	sktemp := make([]*mkrlwe.SecretKey, JoiningParties)
	pktemp := make([]*mkrlwe.PublicKey, JoiningParties)
	rlktemp := make([]*mkrlwe.RelinearizationKey, JoiningParties)
	cjktemp := make([]*mkrlwe.ConjugationKey, JoiningParties)
	rtkstemp := make([]map[uint]*mkrlwe.RotationKey, JoiningParties)

	for p := 0; p < JoiningParties; p++ { //generate additional joining party's keys...
		sktemp[p], pktemp[p] = testContext2.kgen.GenKeyPair("group0")
		rlktemp[p] = testContext2.kgen.GenRelinearizationKey(sktemp[p])
		cjktemp[p] = testContext2.kgen.GenConjugationKey(sktemp[p])
		rtkstemp[p] = testContext2.kgen.GenDefaultRotationKeys(sktemp[p])
	}

	Update_KG_end := time.Since(Update_KG_start)
	fmt.Print("Extend (key) Generation time = ", Update_KG_end, "\n")

	for p := 0; p < numParties; p++ {
		skup[p] = sk[p]
		pkup[p] = pk[p]
		rlkup[p] = rlk[p]
		cjkup[p] = cjk[p]
		rtksup[p] = rtks[p]
		swkup[p] = swk[p]
		swkheadup[p] = swkhead[p]
	}

	for p := 0; p < JoiningParties; p++ {
		skup[numParties+p] = sktemp[p]
		pkup[numParties+p] = pktemp[p]
		rlkup[numParties+p] = rlktemp[p]
		cjkup[numParties+p] = cjktemp[p]
		rtksup[numParties+p] = rtkstemp[p]
	}

	gsktemp := gsk.CopyNew()
	params.RingQP().AddLvl(levelQ, levelP, gsk.Value, skup[numParties+JoiningParties-1].Value, gsktemp.Value)
	testContext2.skSet.AddSecretKey(gsktemp)

	params.RingQP().AddLvl(levelQ, levelP, gpk.Value[0], pkup[numParties+JoiningParties-1].Value[0], gpk.Value[0])
	testContext2.pkSet.AddPublicKey(gpk)

	for idx, _ := range rtksup[0] {
		rtk := make([]*mkrlwe.RotationKey, numParties+JoiningParties)
		for p := 0; p < numParties+JoiningParties; p++ {
			rtk[p] = rtksup[p][idx]
		}
		for i := 0; i < beta; i++ {
			params.RingQP().AddLvl(levelQ, levelP, grtk.Value.Value[i], rtk[numParties+JoiningParties-1].Value.Value[i], grtk.Value.Value[i])
		}
		testContext.rtkSet.AddRotationKey(grtk)
	}
	for i := 0; i < beta; i++ {
		params.RingQP().AddLvl(levelQ, levelP, grlk.Value[0].Value[i], rlkup[numParties+JoiningParties-1].Value[0].Value[i], grlk.Value[0].Value[i]) // 인자에 추가
		params.RingQP().AddLvl(levelQ, levelP, grlk.Value[1].Value[i], rlkup[numParties+JoiningParties-1].Value[1].Value[i], grlk.Value[1].Value[i]) // 인자에 추가
		params.RingQP().AddLvl(levelQ, levelP, grlk.Value[2].Value[i], rlkup[numParties+JoiningParties-1].Value[2].Value[i], grlk.Value[2].Value[i]) // 인자에 추가
		params.RingQP().AddLvl(levelQ, levelP, gcjk.Value.Value[i], cjkup[numParties+JoiningParties-1].Value.Value[i], gcjk.Value.Value[i])
	}
	testContext2.rlkSet.AddRelinearizationKey(grlk)
	testContext2.cjkSet.AddConjugationKey(gcjk)

	////////////////////////// SWK //////////////////////////////////////
	for p := numParties; p < numParties+JoiningParties; p++ { //for each group...
		testContext2.swkSet[p] = mkrlwe.NewSWKSet()
		testContext2.swkheadSet[p] = mkrlwe.NewSWKSet()
	}

	for p := numParties; p < numParties+JoiningParties; p++ {
		swk[p], swkhead[p] = testContext.kgen.GenSWK(skup[p], gpk) // testContext.pkSet.GetPublicKey("group0"))
		// swk[p], swkhead[p] = testContext.kgen.GenSWKTest(sk[p], gsk) //testContext.skSet.GetSecretKey("group0"))
		testContext2.swkSet[p].AddSWK(swk[p])
		testContext2.swkheadSet[p].AddSWK(swkhead[p])
		swkup[p] = swk[p]
		swkheadup[p] = swkhead[p]
	}

	// uaux key gen
	jk = mkrlwe.NewSWK(params.Parameters, "group0")
	jkhead = mkrlwe.NewSWK(params.Parameters, "group0")

	uaux, uauxhead = testContext.kgen.UAuxKeyGen(swkheadsum, skup[numParties+JoiningParties-1])

	// jk <- swk + uaux
	for i := 0; i < beta; i++ {
		ringQP.AddLvl(levelQ, levelP, swksum.Value.Value[i], uaux.Value.Value[i], jk.Value.Value[i])
		jkhead.Value.Value[i].Q.Copy(swkheadsum.Value.Value[i].Q)
		jkhead.Value.Value[i].P.Copy(swkheadsum.Value.Value[i].P)
	}

	// swk_i update
	swkaux := make([]*mkrlwe.SWK, numParties)
	swkauxhead := make([]*mkrlwe.SWK, numParties)
	for p := 0; p < numParties; p++ {
		swkaux[p], swkauxhead[p] = testContext.kgen.UAuxKeyGen(swkhead[p], skup[numParties+JoiningParties-1])
		for i := 0; i < beta; i++ {
			ringQP.AddLvl(levelQ, levelP, swk[p].Value.Value[i], swkaux[p].Value.Value[i], swk[p].Value.Value[i])
		}
	}

	// Update swksum
	for p := numParties; p < numParties+JoiningParties; p++ {
		for i := 0; i < beta; i++ {
			params.RingQP().AddLvl(levelQ, levelP, swksum.Value.Value[i], swk[p].Value.Value[i], swksum.Value.Value[i])
			params.RingQP().AddLvl(levelQ, levelP, swkheadsum.Value.Value[i], swkhead[p].Value.Value[i], swkheadsum.Value.Value[i]) // 필요없을듯
		}
	}

	// Update Ciphertext
	Update_ctxt_start := time.Now()
	ctxtListup = make([]*Ciphertext, len(ctxtList))
	for k := range ctxtList {
		ctxtListup[k] = testContext2.evaluator.KSNew(ctxtList[k], jk, jkhead)
	}

	// for k := range ctxtList {
	// 	// ptxt := testContext.decryptor.ptxtPool
	// 	ctdecList := make([]*Ciphertext, 2)
	// 	level := ctxtList[k].Level()
	// 	// ptxt.Plaintext.Value.Coeffs = ptxt.Plaintext.Value.Coeffs[:level+1]

	// 	for p := 0; p < 2; p++ {
	// 		ctdecList[p] = ctxtList[k].CopyNew()
	// 	}
	// 	testContext.decryptor.PartialDecryptIP(ctdecList[1], skup[numParties+JoiningParties-1])
	// 	testContext.ringQ.SubLvl(level, ctdecList[0].Value["0"], ctdecList[1].Value["group0"], ctdecList[0].Value["0"])
	// 	ctxtListup[k] = ctdecList[0].CopyNew()
	// }
	Update_ctxt_end := time.Since(Update_ctxt_start)
	fmt.Print("Extend (ctxt) time = ", Update_ctxt_end, "\n")

	swkup = swk
	swkheadup = swkhead
	swksumup = swksum
	swkheadsumup = swkheadsum
	jkup = jk
	jkheadup = jkhead
	grlkup = grlk
	gcjkup = gcjk
	grtkup = grtk
	gskup = gsktemp
	gpkup = gpk
	uauxup = uaux
	uauxheadup = uauxhead

	if testContext2.prng, err = utils.NewPRNG(); err != nil {
		return nil, err, gskup, gpkup, grlkup, gcjkup, grtkup, skup, pkup, rlkup, cjkup, swkup, swkheadup, swksumup, swkheadsumup, rtksup, jkup, jkheadup, uauxup, uauxheadup, ctxtListup
	}

	testContext2.encryptor = testContext.encryptor
	testContext2.decryptor = testContext.decryptor
	testContext2.evaluator = testContext.evaluator
	testContext2.ringP = testContext.ringP
	testContext2.ringQ = testContext.ringQ

	return testContext2, nil, gskup, gpkup, grlkup, gcjkup, grtkup, skup, pkup, rlkup, cjkup, swkup, swkheadup, swksumup, swkheadsumup, rtksup, jkup, jkheadup, uauxup, uauxheadup, ctxtListup
}

func testJoinPartyMK(testContext *testParams,
	sk []*mkrlwe.SecretKey, pk []*mkrlwe.PublicKey, rlk []*mkrlwe.RelinearizationKey, cjk []*mkrlwe.ConjugationKey, rtks []map[uint]*mkrlwe.RotationKey,
	groupIdSet *mkrlwe.IDSet, groupList []string,
	numParties int, JoiningParties int, t *testing.T) (testContextout *testParams, groupIdSetup *mkrlwe.IDSet, err error,
	skup []*mkrlwe.SecretKey, pkup []*mkrlwe.PublicKey, rlkup []*mkrlwe.RelinearizationKey, cjkup []*mkrlwe.ConjugationKey, rtksup []map[uint]*mkrlwe.RotationKey) {

	groupListup := make([]string, *maxGroups+1)
	idsetup := mkrlwe.NewIDSet()
	for i := range groupList {
		groupListup[i] = groupList[i]
		idsetup.Add(groupListup[i])
	}
	for i := len(groupList); i < len(groupList)+JoiningParties; i++ {
		groupListup[i] = "group" + strconv.Itoa(i)
		idsetup.Add(groupListup[i])
	}

	for i := len(groupList); i < len(groupList)+JoiningParties; i++ {
		groupId := "group" + strconv.Itoa(i)
		for p := 0; p < numParties; p++ {
			sk[p], pk[p] = testContext.kgen.GenKeyPair(groupId)
			rlk[p] = testContext.kgen.GenRelinearizationKey(sk[p])
			cjk[p] = testContext.kgen.GenConjugationKey(sk[p])
			rtks[p] = testContext.kgen.GenDefaultRotationKeys(sk[p])
		}

		gsk := testContext.kgen.GenGroupSecretKey(sk)
		testContext.skSet.AddSecretKey(gsk)

		gpk := testContext.kgen.GenGroupPublicKey(pk)
		testContext.pkSet.AddPublicKey(gpk)

		grlk := testContext.kgen.GenGroupRelinKey(rlk)
		testContext.rlkSet.AddRelinearizationKey(grlk)

		gcjk := testContext.kgen.GenGroupConjKey(cjk)
		testContext.cjkSet.AddConjugationKey(gcjk)

		for idx, _ := range rtks[0] {
			rtk := make([]*mkrlwe.RotationKey, numParties)
			for p := 0; p < numParties; p++ {
				rtk[p] = rtks[p][idx]
			}
			grtk := testContext.kgen.GenGroupRotKey(rtk)
			testContext.rtkSet.AddRotationKey(grtk)
		}
	}

	testContextout = testContext
	skup = sk
	pkup = pk
	rlkup = rlk
	cjkup = cjk
	rtksup = rtks
	groupIdSetup = groupIdSet

	if testContext.prng, err = utils.NewPRNG(); err != nil {
		return nil, idsetup, err, skup, pkup, rlkup, cjkup, rtksup
	}
	return testContextout, idsetup, nil, skup, pkup, rlkup, cjkup, rtksup
}
