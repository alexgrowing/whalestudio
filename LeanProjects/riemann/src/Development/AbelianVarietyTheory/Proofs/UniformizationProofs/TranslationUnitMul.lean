import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubN_mul_cubN_add {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (k l : ℕ) (b c m y : A) :
    cubN θ k b m y * cubN θ l c m y * θ (b * m ^ k) (c * m ^ l) y = cubN θ (k + l) (b * c) m y * θ b c y := by
  induction k with
  | zero =>
    induction l with
    | zero => simp [cubN]
    | succ l ih =>
      have e := h.coc b (c * m ^ l) m y
      simp only [cubN, Finset.prod_range_succ, Finset.prod_range_zero, Nat.zero_add, pow_zero, _root_.mul_one,
        _root_.one_mul] at ih ⊢
      rw [pow_succ m, ← _root_.mul_assoc c, _root_.mul_assoc b c]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have e' := congrArg Additive.ofMul e
      simp only [_root_.mul_assoc b c] at ih'
      simp only [ofMul_mul, _root_.mul_assoc b c] at ih' e' ⊢
      linear_combination (norm := abel) ih' - e'
  | succ k ih =>
    have e := h.coc m (b * m ^ k) (c * m ^ l) y
    have p₁ : m * (b * m ^ k) = b * m ^ (k + 1) := by rw [pow_succ, mul_comm m, _root_.mul_assoc]
    have p₂ : b * m ^ k * (c * m ^ l) = b * c * m ^ (k + l) := by rw [pow_add, _root_.mul_mul_mul_comm]
    rw [p₁, p₂, h.s01 m, h.s01 m] at e
    rw [Nat.add_right_comm]
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at ih' e' ⊢
    linear_combination (norm := abel) ih' + e'

theorem translationUnit_mul :
    ∀ (A U : Type) [CommGroup A] [CommGroup U] (θ : A → A → A → U), IsCub θ → ∀ (k l : ℕ) (b c m y : A), (cubN θ k b m y * (θ b y m)⁻¹) * (cubN θ l c m y * (θ c y m)⁻¹) * θ (b * m ^ k) (c * m ^ l) y * θ b c m = θ b c (y * m) * (cubN θ (k + l) (b * c) m y * (θ (b * c) y m)⁻¹) := by
  intro A U _ _ θ h k l b c m y
  have a := congrArg Additive.ofMul (cubN_mul_cubN_add h k l b c m y)
  have e := congrArg Additive.ofMul (h.compat b c y m)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a e ⊢
  linear_combination (norm := abel) a + e

end GlobalTheory
