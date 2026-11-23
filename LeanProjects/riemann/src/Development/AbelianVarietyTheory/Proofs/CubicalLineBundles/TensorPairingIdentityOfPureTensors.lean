import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.LamCalc

theorem isTensor_induction {S : Scheme.{0}} {O : Type} [CommRing O] {G A T : Over S} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} {M : Type} [AddCommGroup M] [Module O M]
    (t : Serre.IsTensor A b G a M) {P : (T ⟶ A) → Prop} (y : T ⟶ A)
    (tmul : ∀ (m : M) (x : T ⟶ G), P (x ≫ t.tmul m)) (mul : ∀ y z, P y → P z → P (y * z)) : P y := by
  refine t.induction_on y ?_ tmul mul
  have h := tmul 0 1
  rwa [t.tmul_zero, MonObj.comp_one] at h

theorem lamEq_of_tmul : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (b' : OAct O A') (M' : Type) [AddCommGroup M'] [Module O M'] (t' : Serre.IsTensor A' b' G a M') (B B' : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : LB B.left) (L' : LB B'.left) (f₁ : A ⟶ B) (f₂ : A' ⟶ B) (g₁ : A ⟶ B') (g₂ : A' ⟶ B'), L.IsLB → L'.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → (∃ t : LB.Gen (Theta B' L'), t.IsGen) → IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
  (∀ m m', LamEq L (t.tmul m ≫ f₁) (t'.tmul m' ≫ f₂) L' (t.tmul m ≫ g₁) (t'.tmul m' ≫ g₂)) → LamEq L f₁ f₂ L' g₁ g₂ := by
  intro S O _ G A _ _ _ _ a b M _ _ t A' _ _ b' M' _ _ t' B B' _ _ _ _ L L' f₁ f₂ g₁ g₂ hL hL' hT hT' _ _ _ _ h
  have key : ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ A'),
      LBIso (cubeLB B ![x ≫ f₁, y ≫ f₂] L) (cubeLB B' ![x ≫ g₁, y ≫ g₂] L') := by
    intro T x y
    refine isTensor_induction t
      (P := fun x => LBIso (cubeLB B ![x ≫ f₁, y ≫ f₂] L) (cubeLB B' ![x ≫ g₁, y ≫ g₂] L')) x
      (fun m u => ?_) (fun x x' hx hx' => ?_)
    · refine isTensor_induction t'
        (P := fun y => LBIso (cubeLB B ![(u ≫ t.tmul m) ≫ f₁, y ≫ f₂] L)
          (cubeLB B' ![(u ≫ t.tmul m) ≫ g₁, y ≫ g₂] L')) y (fun m' v => ?_) (fun y y' hy hy' => ?_)
      · simp only [Category.assoc]
        exact lbIso_of_lamEq (h m m') u v
      · simp only [MonObj.mul_comp]
        exact lbIso_cubeLB_mul_right_of hL hL' hT hT' hy hy'
    · simp only [MonObj.mul_comp]
      exact lbIso_cubeLB_mul_left_of hL hL' hT hT' hx hx'
  exact key _ (fst A A') (snd A A')

end GlobalTheory.LamCalc
end
