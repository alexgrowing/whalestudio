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

theorem cubN_descent_telescope {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (θ : A → A → A → U)
    (θ' : A' → A' → A' → U) (q : A →* A') (W : A → U) (hc : IsCub θ')
    (h : ∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 =
      W (x * y * u) * W x * W y * W u * θ x y u) (k : ℕ) (x y : A) (hx : q x = 1) :
    cubN θ k 1 x y * W (x ^ k * y) * W x ^ k * W y ^ k * W 1 = W (x ^ k) * W y * W (x * y) ^ k * W 1 ^ k := by
  induction k with
  | zero => simp [cubN, mul_comm]
  | succ k ih =>
    have e := h (x ^ k) x y
    rw [hx, hc.face₂, _root_.one_mul, ← pow_succ] at e
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ (W x), pow_succ (W y), pow_succ (W (x * y)), pow_succ (W 1)]
    generalize (∏ i ∈ Finset.range k, θ (x ^ i) x y) = P at ih ⊢
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul ih
    have a2 := congrArg Additive.ofMul e
    simp only [ofMul_mul] at a1 a2 ⊢
    linear_combination (norm := abel) a1 - a2

theorem cubN_descent_opposite : ∀ (A A' U : Type) [CommGroup A] [CommGroup A'] [CommGroup U] (θ : A → A → A → U) (θ' : A' → A' → A' → U) (q : A →* A') (W : A → U), IsCub θ' → (∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * θ x y u) → ∀ (k : ℕ) (x y : A), q x = 1 → cubN θ k 1 x y * θ y (x ^ k) (x ^ k)⁻¹ * W y ^ (k + 1) * W x ^ k * W (x ^ k)⁻¹ = W (x * y) ^ k * W (y * (x ^ k)⁻¹) * W 1 ^ (k + 1) := by
  intro A A' U _ _ _ θ θ' q W hc h k x y hx
  have t := cubN_descent_telescope θ θ' q W hc h k x y hx
  have e := h y (x ^ k) (x ^ k)⁻¹
  rw [map_pow, hx, one_pow, hc.face₂, _root_.one_mul, mul_inv_cancel, mul_inv_cancel_right, mul_comm y (x ^ k)] at e
  rw [pow_succ (W y), pow_succ (W 1)]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul t
  have a2 := congrArg Additive.ofMul e
  simp only [ofMul_mul] at a1 a2 ⊢
  linear_combination (norm := abel) a1 - a2

end GlobalTheory
