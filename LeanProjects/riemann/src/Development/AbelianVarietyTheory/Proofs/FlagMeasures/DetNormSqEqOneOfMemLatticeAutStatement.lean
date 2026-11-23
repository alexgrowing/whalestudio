import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetNormSqEqOneOfMemLatticeAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsLattice E Λ → ∀ γ ∈ autGL E j Λ, detNorm E j γ = 1 := by
  first | exact @GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL | exact GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL | (intros; apply GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL <;> assumption)
