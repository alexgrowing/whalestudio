import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace GmPoints

variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem unitOf_val (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    (unitOf w : R) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (w.left.appTop.hom (charUnit (Spec (CommRingCat.of O)) (ULift ℤ) (ULift.up 1)).val) := by
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Spec (CommRingCat.of R)).presheaf.map (𝟙 (Opposite.op ⊤))).hom
      (w.left.appTop.hom (charUnit (Spec (CommRingCat.of O)) (ULift ℤ) (ULift.up 1)).val)) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem evalOne_bijective {M : Type} [Group M] :
    Function.Bijective (fun f : Multiplicative (ULift.{0} ℤ) →* M =>
      f (Multiplicative.ofAdd (ULift.up 1))) := by
  have h : ∀ n : ℤ, (Multiplicative.ofAdd (ULift.up n) : Multiplicative (ULift.{0} ℤ)) =
      (Multiplicative.ofAdd (ULift.up 1)) ^ n := by
    intro n
    rw [← ofAdd_zsmul]
    congr 1
    ext
    simp
  constructor
  · intro f g hfg
    ext ⟨n⟩
    have := h n
    change f (Multiplicative.ofAdd (ULift.up n)) = g (Multiplicative.ofAdd (ULift.up n))
    rw [this, map_zpow, map_zpow]
    exact congrArg (· ^ n) hfg
  · intro m
    exact ⟨{ toFun := fun x => m ^ x.toAdd.down
             map_one' := zpow_zero m
             map_mul' := fun x y => zpow_add m _ _ }, zpow_one m⟩

theorem unitOf_eq (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    unitOf w = Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv
      (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R) w
        (Multiplicative.ofAdd (ULift.up 1))) := by
  ext
  rw [unitOf_val, ← splitTorusPointsEquiv_val]
  rfl

theorem unitOf_bijective :
    Function.Bijective (unitOf : (specO O R ⟶ Gm (Spec (CommRingCat.of O))) → Rˣ) := by
  rw [funext (unitOf_eq (O := O) (R := R))]
  exact (Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv).bijective.comp
    (evalOne_bijective.comp
      (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R)).bijective)

theorem unitOf_mul (w w' : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    unitOf (w * w') = unitOf w * unitOf w' := by
  rw [unitOf_eq, unitOf_eq, unitOf_eq]
  refine Eq.trans ?_ (map_mul _ _ _)
  congr 1
  exact DFunLike.congr_fun (map_mul
    (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R)) w w') _

theorem unitOf_ptMap {R' : Type} [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R')
    (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    (unitOf (ptMap φ ≫ w) : R') = φ (unitOf w : R) := by
  rw [unitOf_val, unitOf_val, Over.comp_left, Scheme.Hom.comp_appTop]
  exact congrArg (fun g : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of R' => g.hom _)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom))

end GmPoints

theorem unitOf_bijective_mul_natural :
    ∀ (O : Type) [CommRing O], (∀ (R : Type) [CommRing R] [Algebra O R], Function.Bijective (unitOf : (specO O R ⟶ Gm (Spec (CommRingCat.of O))) → Rˣ) ∧ ∀ w w' : specO O R ⟶ Gm (Spec (CommRingCat.of O)), unitOf (w * w') = unitOf w * unitOf w') ∧ ∀ (R R' : Type) [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R') (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))), (unitOf (ptMap φ ≫ w) : R') = φ (unitOf w : R) :=
  fun _ _ => ⟨fun _ _ _ => ⟨GmPoints.unitOf_bijective, GmPoints.unitOf_mul⟩,
    fun _ _ _ _ _ _ φ w => GmPoints.unitOf_ptMap φ w⟩

end GlobalTheory
