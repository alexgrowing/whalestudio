import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqSemisimpleCuspFormsGamma1
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTq_semisimple_cuspForms_gamma1 : ∀ (N k q : ℕ) (σ : SL(2, ℤ)), 5 ≤ N → 3 ≤ k → q.Prime → ¬ q ∣ N → IsDiam N 1 (q : ZMod N) σ → ∀ (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne.tq_semisimple | exact GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne.tq_semisimple | (intros; apply GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne.tq_semisimple <;> assumption)
