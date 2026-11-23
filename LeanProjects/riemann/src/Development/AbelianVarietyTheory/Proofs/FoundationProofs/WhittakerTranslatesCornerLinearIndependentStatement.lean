import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WhittakerTranslatesCornerLinearIndependent
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_translates_corner_linearIndependent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ (L : Lev g N), L.sharp = false → ∀ (x : M), x ≠ 0 → (∀ u, IsUp g N u → ρ u x = L.chi u • x) → ∀ k : ℕ, k < N → ∀ φ : GG g N → ℂ, (∀ h, φ h ≠ 0 → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (h : GG g N).val a b = if a = b then 1 else 0)) → ∑ h, φ h • ρ h x = 0 → ∀ h₀ : GG g N, ∑ u ∈ Finset.univ.filter (fun u : GG g N => IsUp g N u ∧ (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0)), φ (h₀ * u) * L.chi u = 0 := by
  first | exact @GlobalTheory.BadShare.Indep.translates_independent | exact GlobalTheory.BadShare.Indep.translates_independent | (intros; apply GlobalTheory.BadShare.Indep.translates_independent <;> assumption)
