import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseCurvatureTermsSumZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_curvature_terms_sum_zero : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} (β : Fin n → E) {φ : E → ℂ} {b : E}, ContDiffAt ℝ 2 φ b → ∀ (w : Ext (n + n + g)), ∑ i, (baseD β (fun b' => d10 φ b' (β i)) b (wedge (dt g i) w) + baseD β (fun b' => d01 φ b' (β i)) b (wedge (dtb g i) w)) = 0 := by
  first | exact @GlobalTheory.BaseSecondDeriv.baseD_baseD_eq_zero | exact GlobalTheory.BaseSecondDeriv.baseD_baseD_eq_zero | (intros; apply GlobalTheory.BaseSecondDeriv.baseD_baseD_eq_zero <;> assumption)
