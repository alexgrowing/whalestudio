import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_rationalTranslate_mem : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}, Crv D cc δ → ∀ {N N' : ℕ} {x : VC D N N'} {M : ℕ}, 0 < M → M • x ∈ La0 D (tor0 D cc δ) N N' → ∀ {F : VC D N N' → ℂ}, F ∈ TT D (tor0 D cc δ) N N' → Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) N N' := by
  first | exact @GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT | exact GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT | (intros; apply GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT <;> assumption)
