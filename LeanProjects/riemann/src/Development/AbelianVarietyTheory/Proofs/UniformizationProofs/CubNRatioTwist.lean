import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem cubN_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) * W (a * b) * W (a * d) * W (b * d) * W 1 =
      W (a * b * d) * W a * W b * W d * θ' a b d) (x y : A') (k : ℕ) :
    cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k =
      W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y := by
  induction k with
  | zero => simp only [cubN, Finset.range_zero, Finset.prod_empty, pow_zero, _root_.one_mul, _root_.mul_one]; exact mul_comm _ _
  | succ k ih =>
    have e₁ : cubN θ (k + 1) 1 (β x) (β y) = cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, map_pow]
    have e₂ : cubN θ' (k + 1) 1 x y = cubN θ' k 1 x y * θ' (x ^ k) x y := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have H := hθ (x ^ k) x y
    rw [← pow_succ] at H
    rw [e₁, e₂]
    apply mul_right_cancel (b := W (x ^ k) * W (x ^ k * y))
    calc cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W y *
            (W (x * y) * W 1) ^ (k + 1) * (W (x ^ k) * W (x ^ k * y))
          = (cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k) *
            (θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W (x ^ k * y) * W (x * y) * W 1) := by
          rw [pow_succ (W (x * y) * W 1) k]; ac_rfl
      _ = (W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y) *
            (W (x ^ (k + 1) * y) * W (x ^ k) * W x * W y * θ' (x ^ k) x y) := by rw [ih, H]
      _ = W (x ^ (k + 1) * y) * W 1 * (W x * W y) ^ (k + 1) * (cubN θ' k 1 x y * θ' (x ^ k) x y) *
            (W (x ^ k) * W (x ^ k * y)) := by
          rw [pow_succ (W x * W y) k]; ac_rfl

theorem cubN_ratio_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) * W (a * b) * W (a * d) * W (b * d) * W 1 =
      W (a * b * d) * W a * W b * W d * θ' a b d) {x y : A'} {N : ℕ} (hx : x ^ N = 1) (hy : y ^ N = 1) {e : U}
    (h : e * cubN θ' N 1 x y = cubN θ' N 1 y x) :
    e * cubN θ N 1 (β x) (β y) = cubN θ N 1 (β y) (β x) := by
  have h₁ := cubN_twist β W hθ x y N
  have h₂ := cubN_twist β W hθ y x N
  simp only [hx, _root_.one_mul] at h₁
  simp only [hy, _root_.one_mul] at h₂
  rw [mul_comm y x, mul_comm (W y) (W x)] at h₂
  have k₁ : cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 x y := by
    apply mul_right_cancel (b := W 1 * W y)
    calc cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N * (W 1 * W y)
          = cubN θ N 1 (β x) (β y) * W 1 * W y * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W y * W 1 * (W x * W y) ^ N * cubN θ' N 1 x y := h₁
      _ = (W x * W y) ^ N * cubN θ' N 1 x y * (W 1 * W y) := by ac_rfl
  have k₂ : cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 y x := by
    apply mul_right_cancel (b := W 1 * W x)
    calc cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N * (W 1 * W x)
          = cubN θ N 1 (β y) (β x) * W 1 * W x * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W x * W 1 * (W x * W y) ^ N * cubN θ' N 1 y x := h₂
      _ = (W x * W y) ^ N * cubN θ' N 1 y x * (W 1 * W x) := by ac_rfl
  apply mul_right_cancel (b := (W (x * y) * W 1) ^ N)
  calc e * cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N
        = e * (cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N) := mul_assoc _ _ _
    _ = (W x * W y) ^ N * (e * cubN θ' N 1 x y) := by rw [k₁]; ac_rfl
    _ = cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N := by rw [h, k₂]

theorem cubWeil_map : (∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (P : CP G) (P' : CP G') (F : G'.left ⟶ G.left) (hw) (w), IsCPMap P' P f F hw w → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil P'.c N x y ζ → CubWeil P.c N (toBase hw x) (toBase hw y) ζ) := by
  intro S S' f G _ _ G' _ _ P P' F hw w hP N T x y ζ hζ
  obtain ⟨hx, hy, hr⟩ := hζ
  let β := toBaseHom (hw := hw) hP.mul T
  have hβ : ∀ a : T ⟶ G', β a = toBase hw a := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hβ, ← map_pow, hx, map_one]
  · rw [← hβ, ← map_pow, hy, map_one]
  · intro z J hJ
    obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
    have hv := (hP.vals T z J' J hJ' hJ (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (fun _ => rfl)).2.2
    exact cubN_ratio_twist β (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (θ := cubV P.c (T := Over.mk (T.hom ≫ f)) z J) (θ' := cubV P'.c z J') hv hx hy (hr z J' hJ')

end GlobalTheory.UU
