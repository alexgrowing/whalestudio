import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEvalCompEqEvAMap
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_eval_eq_evA_map_of_isEval_of_pow_eq_zero : ∀ (p m : ℕ) (O A k A' σ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing k] [CommRing A'] [Algebra k A'] [Fintype σ] (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A), IsEval p x E → ∀ (r : O →+* k) (g : A →+* A'), (∀ c, g (algebraMap O A c) = algebraMap k A' (r c)) → (p : A') ^ m = 0 → ∀ hx : ∀ i, IsNilpotent (g (x i)), ∀ f, g (E f) = evA k (fun i => g (x i)) hx (map r f) := by
  first | exact @GlobalTheory.algHom_eval_comp_eq_evA_map | exact GlobalTheory.algHom_eval_comp_eq_evA_map | (intros; apply GlobalTheory.algHom_eval_comp_eq_evA_map <;> assumption)
