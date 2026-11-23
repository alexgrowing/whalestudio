import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in

private theorem biextVal_pull {S : Scheme.{0}} {G : Over S} {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → ((G ⊗ G ⊗ G).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J : (T'.left ⟶ X) → L.ι} (hJ : Good L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L φ ε t (lift x (lift x' y)).left) ρ.left z J =
      val t (lift (ρ ≫ x) (lift (ρ ≫ x') (ρ ≫ y))).left z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift]

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem biext_val_axioms :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) := by
  intro S G _ _ P β T z J hJ t₁ t₂ h₁ h₂
  have a₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 0 = a := fun a b c d => by simp [x4]
  have a₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 1 = b := fun a b c d => by simp [x4]
  have a₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 2 = c := fun a b c d => by simp [x4]
  have a₃ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 3 = d := fun a b c d => by simp [x4]
  have b₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 0) (x4 G 1) = a * b :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  have b₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 1) (x4 G 2) = b * c :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  have b₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 2) (x4 G 3) = c * d :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃])
  have c₀ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 0 = a := fun a b c => by simp [x3]
  have c₁ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 1 = b := fun a b c => by simp [x3]
  have c₂ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 2 = c := fun a b c => by simp [x3]
  simp only [h₁, h₂]
  refine ⟨fun x x' x'' y => ?_, fun x x' y => ?_, fun x y y' y'' => ?_, fun x y y' => ?_, fun x x' y y' => ?_⟩
  · have := val_corr hJ β.assoc1 (lift x (lift x' (lift x'' y))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm1 (lift x (lift x' y)).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.assoc2 (lift x (lift y (lift y' y''))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₁, b₂, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm2 (lift x (lift y y')).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.compat (lift x (lift x' (lift y y'))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))).symm.trans
      (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₂, a₀, a₁, a₂, a₃] at e

end GlobalTheory
