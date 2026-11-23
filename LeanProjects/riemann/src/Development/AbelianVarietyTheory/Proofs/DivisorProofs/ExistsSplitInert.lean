import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEigenvectorUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecMemThetaSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOverCosetRepresentativesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesConjCosetVector

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7}

theorem cosetVec_mem_TT {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (o : ℕ) :
    cosetVec P 𝔪 o ∈ TT D (tor0 D ⊤ δ) P.a P.d :=
  GlobalTheory.T.cosetVec_mem_theta_space P h𝔪 o

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m)

end GlobalTheory.FunObj.NormUniq

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7}

end GlobalTheory.FunObj.NormUniq

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m)

end GlobalTheory.FunObj.NormUniq
