import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubeRel_even_nsmul {X : Type} [AddCommGroup X] (φ : X → ℤ)
    (h : ∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c))
    (he : ∀ a, φ (-a) = φ a) (a : X) (n : ℕ) : φ (n • a) = (n : ℤ) ^ 2 * φ a := by
  have h0 : φ 0 = 0 := by
    have := h 0 0 0
    simp only [add_zero] at this
    linarith
  have key : ∀ n : ℕ, φ (n • a) = (n : ℤ) ^ 2 * φ a ∧
      φ ((n + 1) • a) = ((n + 1 : ℕ) : ℤ) ^ 2 * φ a := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 := h ((n + 1) • a) a (-a)
      have e1 : (n + 1) • a + a + -a = (n + 1) • a := by abel
      have e2 : (n + 1) • a + a = (n + 1 + 1) • a := (succ_nsmul a (n + 1)).symm
      have e3 : (n + 1) • a + -a = n • a := by rw [succ_nsmul]; abel
      rw [e1, e2, e3, add_neg_cancel, he, h0, ih.1, ih.2] at h1
      push_cast at h1 ⊢
      linear_combination -h1
  exact (key n).1

theorem even_quadratic_pos_of_finite_nonpos : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℤ), (∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c)) → (∀ a, φ (-a) = φ a) → {a | φ a ≤ 0}.Finite → ∀ a, a ≠ 0 → 0 < φ a := by
  intro X _ _ φ h he hfin a ha
  by_contra hle
  rw [not_lt] at hle
  have hinj : Function.Injective (fun n : ℕ => n • a) := by
    intro m n hmn
    have h1 : ((m : ℤ) - (n : ℤ)) • a = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul]
      exact sub_eq_zero.mpr hmn
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact_mod_cast sub_eq_zero.mp h2
    · exact absurd h2 ha
  refine Set.infinite_of_injective_forall_mem hinj ?_ hfin
  intro n
  show φ (n • a) ≤ 0
  rw [cubeRel_even_nsmul φ h he a n]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle

end GlobalTheory
