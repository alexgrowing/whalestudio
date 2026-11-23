import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsBalancedFormsUptoAut
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiser_systems_balanced_forms_upto_aut : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ b ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b x x) → ∃ e : Y ≃ₗ[O] Y, ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → pull e.toLinearMap b (μ cl) (μ cl) ≤ pull e.toLinearMap b α α) → μ ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut | exact GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut | (intros; apply GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut <;> assumption)
