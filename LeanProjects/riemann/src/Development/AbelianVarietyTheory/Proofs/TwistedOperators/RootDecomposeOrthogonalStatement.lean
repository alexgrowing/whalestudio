import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootDecomposeOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_decompose_orthogonal : ∀ {k : ℕ} {T : Finset (SV k)} {u v : SV k}, IsPar T → u ∈ T → v ∈ T → v ≠ u →
  ∃ κ : ℝ, 0 < κ ∧ ∃ t : ℝ, rt T v = κ • rt (T.erase u) v + t • rt T u ∧ ⟪rt (T.erase u) v, rt T u⟫_ℝ = 0 := by
  first | exact @GlobalTheory.Chamber.rt_eq_smul_rt_erase_add | exact GlobalTheory.Chamber.rt_eq_smul_rt_erase_add | (intros; apply GlobalTheory.Chamber.rt_eq_smul_rt_erase_add <;> assumption)
