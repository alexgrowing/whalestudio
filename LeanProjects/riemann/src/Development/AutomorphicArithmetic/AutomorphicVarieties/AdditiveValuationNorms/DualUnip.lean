import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Formalism.GaloisCohomology.Statement
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.DualDiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.TorsFin

open UpperTheory.V UpperTheory.V.PropA Formalism.GaloisCohomology

theorem UpperTheory.V.PropA.dualUnip :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (g : Module.End ℤ_[l] D) (t : Module.End ℤ_[l] (D →ₗ[ℤ_[l]] QZ l)),
      Module.Finite ℤ_[l] (D →ₗ[ℤ_[l]] QZ l) → (∀ x φ, t x φ = x (g φ)) → (∀ φ : D, ∃ k : ℕ, ((g - 1) ^ k) φ = 0) → Unip t := by
  intro l _ D _ _ g t hfin ht hnil
  classical
  have hT := torsFin l D hfin
  choose k hk using hnil
  have key : ∀ (n : ℕ) (x : D →ₗ[ℤ_[l]] QZ l) (φ : D), ((t - 1) ^ n) x φ = x (((g - 1) ^ n) φ) := by
    intro n
    induction n with
    | zero =>
      intro x φ
      simp
    | succ n ih =>
      intro x φ
      rw [pow_succ, Module.End.mul_apply, ih]
      rw [pow_succ' (g - 1), Module.End.mul_apply]
      simp [ht, map_sub]
  refine ⟨hT.toFinset.sup k, fun x => ?_⟩
  obtain ⟨y, hy⟩ := dualDiv l D (((t - 1) ^ (hT.toFinset.sup k)) x) (by
    intro φ hφ
    rw [key]
    have hmem : φ ∈ hT.toFinset := by simpa using hφ
    have hle : k φ ≤ hT.toFinset.sup k := Finset.le_sup hmem
    rw [← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply, hk, map_zero, map_zero])
  exact ⟨y, by simpa using hy⟩
