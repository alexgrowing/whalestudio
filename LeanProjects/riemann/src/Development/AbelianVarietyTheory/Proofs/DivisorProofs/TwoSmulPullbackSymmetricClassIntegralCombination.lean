import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadraticStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.QuadSum

variable {K : Type} [Field K]

theorem hom_finset_sum {B A : AbVar K} {J : Type} (s : Finset J) (g : J → (B ⟶ A)) :
    Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i ∈ s, g i) = ∏ i ∈ s, (g i).hom := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, add_hom, ih]

theorem lam_symm {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  unfold AbVar.lam
  rw [mul_comm x y]
  abel

theorem lam_prod_right {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x : Y ⟶ A.X) {J : Type}
    (s : Finset J) (y : J → (Y ⟶ A.X)) :
    AbVar.lam c x (∏ j ∈ s, y j) = ∑ j ∈ s, AbVar.lam c x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x 1 1 0).2.2.1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x (y a) _ 0).1, ih]

theorem lam_prod_left {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} {J : Type}
    (s : Finset J) (x : J → (Y ⟶ A.X)) (y : Y ⟶ A.X) :
    AbVar.lam c (∏ i ∈ s, x i) y = ∑ i ∈ s, AbVar.lam c (x i) y := by
  rw [lam_symm, lam_prod_right]
  exact Finset.sum_congr rfl (fun i _ => lam_symm c y (x i))

theorem lam_zpow_zpow {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) (m n : ℤ) :
    AbVar.lam c (x ^ m) (y ^ n) = (m * n) • AbVar.lam c x y := by
  rw [(GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y (x ^ m) y y n).2.2.2.2, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x y y m).2.2.2.1, smul_smul,
    mul_comm n m]

end GlobalTheory.AV.QuadSum

theorem GlobalTheory.AV.QuadSum.pull_sum_smul : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (n : ℕ) (f : Fin n → (B ⟶ A)) (m : Fin n → ℤ), 2 • CechPic.pull (Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i, m i • f i)).left c = ∑ i, ∑ j, (m i * m j) • AbVar.lam c (f i).hom (f j).hom := by
  intro K _ B A c hc n f m
  rw [← (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K B A c hc (∑ i, m i • f i) 1).1, QuadSum.hom_finset_sum, QuadSum.lam_prod_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [QuadSum.lam_prod_right]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [zsmul_hom, zsmul_hom, QuadSum.lam_zpow_zpow]
