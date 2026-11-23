import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology
open scoped TensorProduct

namespace UpperTheory.V.K

def cOne (m : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 m, (j + 2)

def KBridge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (D : LData L Ω l), IsTotallyComplex L → HasMuQ l L → ∀ e : ℕ, 1 ≤ e →
      ∃ (K : Type) (_ : AddCommGroup K) (_ : Module ℤ_[l] K) (_ : Finite K)
        (p : K →ₗ[ℤ_[l]] H2 (zlTw D ((e : ℤ) + 1)))
        (h : K →ₗ[ℤ_[l]] ℤ_[l] ⊗[ℤ] HGL L (4 * e + 4) (2 * e)),
        Function.Surjective p ∧ ∀ x, h x = 0 → (l : ℤ_[l]) ^ cOne (2 * e) • x = 0

theorem two_mul_cOne (m : ℕ) : 2 * cOne m = m * (m + 5) := by
  induction m with
  | zero => simp [cOne]
  | succ m ih =>
    unfold cOne at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

theorem cOne_le (m : ℕ) : cOne m ≤ m * (m + 3) := by
  have := two_mul_cOne m
  nlinarith [Nat.zero_le m, Nat.zero_le (m * m)]

end UpperTheory.V.K

end
