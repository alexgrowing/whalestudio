import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TensorFinite

variable {S : Scheme.{0}}

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.TensorFinite.isFinite_of_comp {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated Y.hom]
    (h : IsFinite (f ≫ g).left) : IsFinite f.left := by
  haveI : IsFinite (f.left ≫ g.left) := by rwa [← Over.comp_left]
  haveI : IsSeparated g.left :=
    MorphismProperty.of_postcomp (W := @IsSeparated) (W' := ⊤) (f := g.left) (g := Z.hom)
      (hg := trivial) (hfg := by rw [Over.w g]; infer_instance)
  exact IsFinite.of_comp f.left g.left

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.TensorFinite.isFinite_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y') (hf : IsFinite f.left)
    (hg : IsFinite g.left) : IsFinite (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullback_map (P := @IsFinite) hf hg (Over.w f).symm (Over.w g).symm

theorem id_pow_tensor (G H : Over S) [GrpObj G] [GrpObj H] (n : ℕ) :
    (𝟙 (G ⊗ H)) ^ n = ((𝟙 G) ^ n ⊗ₘ (𝟙 H) ^ n) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.pow_comp, MonObj.comp_pow]

theorem isFinite_id_pow_powObj (G : Over S) [GrpObj G] (n : ℕ) (h : IsFinite ((𝟙 G) ^ n).left) :
    ∀ m : ℕ, IsFinite ((𝟙 (Out.powObj G m)) ^ n).left
  | 0 => by
    have e : (𝟙 (Out.powObj G 0)) ^ n = 𝟙 _ := toUnit_unique (X := Out.powObj G 0) _ _
    rw [e, Over.id_left]
    infer_instance
  | m + 1 => by
    have e : (𝟙 (Out.powObj G (m + 1))) ^ n = ((𝟙 G) ^ n ⊗ₘ (𝟙 (Out.powObj G m)) ^ n) :=
      id_pow_tensor G (Out.powObj G m) n
    rw [e]
    exact isFinite_tensorHom _ _ h (isFinite_id_pow_powObj G n h m)

theorem isFinite_id_pow_of_retract {H K : Over S} [GrpObj H] [GrpObj K] [IsSeparated H.hom]
    [IsSeparated K.hom] (ρ : Retract H K) [IsMonHom ρ.i] (n : ℕ)
    (h : IsFinite ((𝟙 K) ^ n).left) : IsFinite ((𝟙 H) ^ n).left := by
  have hi : IsFinite ρ.i.left := isFinite_of_comp ρ.i ρ.r (by
    rw [ρ.retract, Over.id_left]; infer_instance)
  refine isFinite_of_comp _ ρ.i ?_
  have e : ((𝟙 H) ^ n) ≫ ρ.i = ρ.i ≫ ((𝟙 K) ^ n) := by
    simp [MonObj.pow_comp, MonObj.comp_pow]
  rw [e, Over.comp_left]
  infer_instance

theorem mapLeft_nsmul_id {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H] {a : OAct O G}
    {b : OAct O H} (t : IsTensor H b G a M) (n : ℕ) :
    t.mapLeft t (n • LinearMap.id) = (𝟙 H) ^ n := by
  induction n with
  | zero => rw [zero_smul, IsTensor.mapLeft_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, IsTensor.mapLeft_add, ih, IsTensor.mapLeft_id, pow_succ]

theorem isFinite_mapLeft : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) [IsCommMonObj P.A] (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (A : Over S) [GrpObj A] [IsCommMonObj A] (a : OAct O P.A) (b : OAct O A) (t : IsTensor A b P.A a M) (n k : ℕ) (l : M →ₗ[O] (Fin k → O)) (r : (Fin k → O) →ₗ[O] M), 0 < n → (∀ m, r (l m) = n • m) → IsFinite (t.mapLeft (IsTensor.pow (Out.powIsPowGrp P.A k) a) l).left := by
  intro hL S _ P _ O _ M _ _ _ _ A _ _ a b t n k l r hn hr
  have := P.isAb.proper
  have : IsProper A.hom := t.isProper
  have hpow : ∀ m, IsSeparated (Out.powObj P.A m).hom :=
    powObj_property @IsSeparated inferInstance P.A inferInstance
  have hP : IsFinite ((𝟙 P.A) ^ n).left := (hL.mulN S P n hn).1
  obtain ⟨m, ρ, hi, -⟩ := t.exists_retract
  have := hpow m
  have := hpow k
  have hA : IsFinite ((𝟙 A) ^ n).left :=
    isFinite_id_pow_of_retract ρ n (isFinite_id_pow_powObj P.A n hP m)
  refine isFinite_of_comp _ ((IsTensor.pow (Out.powIsPowGrp P.A k) a).mapLeft t r) ?_
  have e : r ∘ₗ l = n • LinearMap.id := LinearMap.ext hr
  rw [← IsTensor.mapLeft_comp, e, mapLeft_nsmul_id]
  exact hA

end GlobalTheory.TensorFinite
