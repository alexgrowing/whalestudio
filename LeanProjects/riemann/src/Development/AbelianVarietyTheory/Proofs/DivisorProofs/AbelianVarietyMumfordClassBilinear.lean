import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassMulLeft

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem lam_swap_of_comm {K : Type} [Field K] {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  rw [AbVar.lam, AbVar.lam, mul_comm x y]
  abel

noncomputable section

def lamLeftMonoidHom {K : Type} [Field K] (A : AbVar K) (c : Pic A.X.left) {Y : Over (Sp K)} (y : Y ⟶ A.X) :
    (Y ⟶ A.X) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (AbVar.lam c x y)) (fun x x' => by
    rw [← ofAdd_add, lam_mul_left_of_cube])

theorem lam_bilinear : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K)) (x y y' : Y ⟶ A.X) (n : ℤ), AbVar.lam c x (y * y') = AbVar.lam c x y + AbVar.lam c x y' ∧ AbVar.lam c 1 y = 0 ∧ AbVar.lam c x 1 = 0 ∧ AbVar.lam c (x ^ n) y = n • AbVar.lam c x y ∧ AbVar.lam c x (y ^ n) = n • AbVar.lam c x y := by
  intro K _ A c Y x y y' n
  have hL : ∀ x z : Y ⟶ A.X, ∀ m : ℤ, AbVar.lam c (x ^ m) z = m • AbVar.lam c x z := fun x z m => by
    have := map_zpow (lamLeftMonoidHom A c z) x m
    simpa [lamLeftMonoidHom] using congrArg Multiplicative.toAdd this
  have h1 : ∀ z : Y ⟶ A.X, AbVar.lam c 1 z = 0 := fun z => by
    simpa using hL 1 z 0
  refine ⟨?_, h1 y, ?_, hL x y n, ?_⟩
  · rw [lam_swap_of_comm c x, lam_swap_of_comm c x, lam_swap_of_comm c x, lam_mul_left_of_cube]
  · rw [lam_swap_of_comm]; exact h1 x
  · rw [lam_swap_of_comm, hL, lam_swap_of_comm]

end

end GlobalTheory.AV.AbVar
