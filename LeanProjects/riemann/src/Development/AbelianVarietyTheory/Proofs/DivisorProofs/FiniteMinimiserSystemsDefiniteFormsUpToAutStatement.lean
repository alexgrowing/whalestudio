import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAut
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiser_systems_definite_forms_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | exact GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | (intros; apply GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut <;> assumption)
