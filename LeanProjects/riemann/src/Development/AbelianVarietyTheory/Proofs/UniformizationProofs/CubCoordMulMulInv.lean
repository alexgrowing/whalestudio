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

theorem cub_coord_mul_mul_inv : ∀ (A U X : Type) [CommGroup A] [CommGroup U] [AddCommGroup X] (θ : A → A → A → U), IsCub θ → ∀ (H : Type) [CommGroup H] (q : H →* A) (c : X → A), (∀ a b, c (a + b) = c a * c b) → ∀ t : X → H → U, (∀ a b x, t (a + b) x * θ (c a) (c b) (q x) = t a x * t b x) → (∀ a x y, t a (x * y) * θ (c a) (q x) (q y) = t a x * t a y) → ∀ a b x y, t a (x * y) * t b (x * y⁻¹) * (θ (c a) (q x) (q y) * θ (c b) (q x) (q y)⁻¹ * θ (c (a - b)) (c b) (q y)) = t (a + b) x * t (a - b) y * (θ (c a) (c b) (q x) * θ (c b) (q y) (q y)⁻¹) := by
  intro A U X _ _ _ θ h H _ q c _ t h₁ h₂ a b x y
  have e₀ : t b 1 = 1 := by
    have e := h₂ b 1 1
    rw [_root_.mul_one, map_one, h.face₃, _root_.mul_one] at e
    exact (mul_eq_left.mp e.symm)
  have e₁ := h₂ a x y
  have e₂ := h₂ b x y⁻¹
  have e₃ := h₂ b y y⁻¹
  have e₄ := h₁ a b x
  have e₅ := h₁ (a - b) b y
  rw [map_inv] at e₂ e₃
  rw [_root_.mul_inv_cancel, e₀, _root_.one_mul] at e₃
  rw [sub_add_cancel] at e₅
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅
  simp only [ofMul_mul] at a₁ a₂ a₃ a₄ a₅ ⊢
  linear_combination (norm := abel) a₁ + a₂ - a₃ - a₄ + a₅

end GlobalTheory
