import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformCongruenceLevelGamma1CapGamma0
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_congruence_level_gamma1CapGamma0 : ∀ (N l : ℕ) (R : Type) [CommRing R] (Φ : SL(2, ℤ) → MvPolynomial (Fin 2) R), 0 < N → 0 < l → (∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, Φ (δ * δ') = Φ δ + Φ δ') → (∀ γ ∈ Gam N l, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹))) Φ) → ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ Gam N l, ∀ δ ∈ CongruenceSubgroup.Gamma M, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ := by
  first | exact @GlobalTheory.KZ.H3.unif_level | exact GlobalTheory.KZ.H3.unif_level | (intros; apply GlobalTheory.KZ.H3.unif_level <;> assumption)
