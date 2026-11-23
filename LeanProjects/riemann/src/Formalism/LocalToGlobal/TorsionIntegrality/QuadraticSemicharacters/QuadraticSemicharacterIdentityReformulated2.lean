import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlockFirstBlockEmb
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.IteratedDerivLine
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LineRestrLinSubst
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.QuadraticSemicharactersOfProductThetaMem
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.NormLtOne

namespace Formalism.L2.Th1.H

theorem opUMul : OpUMul := heisenbergMul
theorem opUComm : OpUComm := heisenbergComm
theorem opUIsom : OpUIsom := heisenbergIsometry
theorem pullOpU : PullOpU := precompHeisenberg
theorem semiCharBasic : SemiCharBasic := semicharacterBasic
theorem semiHom : SemiHom := semicharacterHom
theorem opUAnalytic : OpUAnalytic := heisenbergAnalytic
theorem matHBasic : MatHBasic := matrixFormBasic
theorem stdHBasic : StdHBasic := standardFormBasic
theorem opUStd : OpUStd := heisenbergStandard
theorem opUBlk4 : OpUBlk4 := heisenbergFourfold

theorem interClass : InterClass := InterClass_of semiHom
theorem repsExist : RepsExist := cosetRepsExist
theorem interReps : InterReps := InterReps_of semiHom
theorem interFixed : InterFixed := InterFixed_of semiHom
theorem interTh : InterTh := InterTh_of semiHom opUAnalytic
theorem thIsom : ThIsom := ThIsom_of opUIsom
theorem charSum : CharSum := characterSum
theorem indexEq : IndexEq := IndexEq_of charSum repsExist
theorem interInv : InterInv := InterInv_of opUComm interReps interFixed repsExist
theorem lineTransport : LineTransport := LineTransport_of interInv interTh

theorem stdSelfDual : StdSelfDual := StdSelfDual_proof
theorem stdSemiChar : StdSemiChar := StdSemiChar_proof
theorem product_theta_mem' : ProductThetaMem := product_theta_mem
theorem thStd : ThStd := ThStd_proof
theorem tens4Mem : Tens4Mem := fourfoldTensorMem
theorem fourthRoot : FourthRoot := fourth_root
theorem alphaQSemi : AlphaQSemi := quadMultiplierSemicharacter
theorem alphaQRules : AlphaQRules := quadMultiplierRules
theorem thetaVector : ThetaVector :=
  ThetaVector_of lineTransport thStd product_theta_mem' stdSelfDual stdSemiChar thIsom fourthRoot

theorem lineUnique : LineUnique := lineUnique'
theorem taylorLine : TaylorLine := taylorLine'
theorem taylorMvLinear : TaylorMvLinear := TaylorMvLinear_of lineUnique taylorLine
theorem taylorMvMul : TaylorMvMul := TaylorMvMul_of lineUnique taylorLine
theorem taylorMvComp : TaylorMvComp := TaylorMvComp_of lineUnique taylorLine
theorem taylorMvProd : TaylorMvProd := TaylorMvProd_of lineUnique taylorLine
theorem taylorMvTens4 : TaylorMvTens4 := TaylorMvTens4_of lineUnique taylorLine
theorem taylorMvInj : TaylorMvInj := TaylorMvInj_of lineUnique taylorLine

theorem quadraticSemicharacter_identity_reformulated₂ : quadraticSemicharacterIdentityReformulated₂ := quadraticSemicharacters_of_productThetaMem product_theta_mem'
theorem quadraticSemicharacters_fact : quadraticSemicharacterIdentity :=
  quadraticSemicharacterIdentity_of_reformulated_of_taylorMv_of_repsExist_of_opUAnalytic quadraticSemicharacter_identity_reformulated₂ taylorMvLinear taylorMvComp taylorMvProd taylorMvTens4 repsExist opUAnalytic

end Formalism.L2.Th1.H
