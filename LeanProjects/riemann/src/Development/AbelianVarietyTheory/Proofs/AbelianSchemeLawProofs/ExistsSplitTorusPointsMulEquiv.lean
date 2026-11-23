import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SplitTorusPoints

open Rosenlicht

theorem ΓSpecIso_inv_comp_specMap {W : Scheme.{0}} {A B : CommRingCat.{0}} (g : W ⟶ Spec B)
    (f : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (g ≫ Spec.map f).appTop =
      f ≫ (Scheme.ΓSpecIso B).inv ≫ g.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S}

theorem map_left_fst {T : Scheme.{0}} (f : S ⟶ T) {A B : Over T} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

theorem exists_mul_factor (a b : Z ⟶ splitTorus S X) :
    ∃ q : Z.left ⟶ (splitTorusAff ZU X ⊗ splitTorusAff ZU X).left,
      q ≫ (fst _ _ : _ ⟶ splitTorusAff ZU X).left = a.left ≫ torusFst S X ∧
      q ≫ (snd _ _ : _ ⟶ splitTorusAff ZU X).left = b.left ≫ torusFst S X ∧
      q ≫ μ[splitTorusAff ZU X].left = (a * b).left ≫ torusFst S X := by
  let F := Over.pullback (toZ S)
  let G := splitTorusAff ZU X
  let m : Z ⟶ F.obj (G ⊗ G) := lift (a : Z ⟶ F.obj G) (b : Z ⟶ F.obj G) ≫ Functor.LaxMonoidal.μ F G G
  have key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom (toZ S)) ≫ g.left =
      (m ≫ F.map g).left ≫ torusFst S X := by
    intro g
    rw [Category.assoc, ← map_left_fst, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  refine ⟨m.left ≫ pullback.fst (G ⊗ G).hom (toZ S), ?_, ?_, ?_⟩
  · rw [key]
    congr 2
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))
  · rw [key]
    congr 2
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))
  · rw [key]
    congr 2

theorem coord_mul_single (a b : Z ⟶ splitTorus S X) (x : X) :
    (coord (a * b)).hom (AddMonoidAlgebra.single x 1) =
      (coord a).hom (AddMonoidAlgebra.single x 1) * (coord b).hom (AddMonoidAlgebra.single x 1) := by
  obtain ⟨q, h1, h2, h3⟩ := exists_mul_factor a b
  let A := torusRing ZU X
  let p : Z.left ⟶ Spec (.of (A ⊗[ZU.{0}] A)) := q ≫ (pullbackSpecIso ZU.{0} A A).hom
  let φ := (Scheme.ΓSpecIso (.of (A ⊗[ZU.{0}] A))).inv ≫ p.appTop
  have e1 : coord a = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h1]
    congr 2
    exact (congrArg (q ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A).symm).trans
      (Category.assoc _ _ _).symm
  have e2 : coord b = CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[ZU.{0}] A ⊗[ZU.{0}] A).toRingHom ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h2]
    congr 2
    exact (congrArg (q ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A).symm).trans
      (Category.assoc _ _ _).symm
  have e3 : coord (a * b) = CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A) ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h3]
    congr 2
  rw [e1, e2, e3]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [← map_mul]
  congr 1
  change Coalgebra.comul (R := ULift.{0} ℤ) (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ)) =
    (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ) ⊗ₜ[ULift.{0} ℤ] (1 : AddMonoidAlgebra (ULift.{0} ℤ) X)) *
    ((1 : AddMonoidAlgebra (ULift.{0} ℤ) X) ⊗ₜ[ULift.{0} ℤ] AddMonoidAlgebra.single x (1 : ULift.{0} ℤ))
  simp

theorem coord_single (t : Z ⟶ splitTorus S X) (x : X) :
    (coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (charUnit S X x).val := by
  rw [TorusInj.charUnit_val, coord, Scheme.Hom.comp_appTop]
  have : (TorusInj.tFst (S := S) X).appLE ⊤ ⊤ (TorusInj.tle _) = (torusFst S X).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this]
  rfl

noncomputable def toHom (t : Z ⟶ splitTorus S X) : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
  ((coord t).hom.toMonoidHom.comp (AddMonoidAlgebra.of (ULift.{0} ℤ) X)).toHomUnits

theorem toHom_val (t : Z ⟶ splitTorus S X) (x : X) :
    (toHom t (Multiplicative.ofAdd x)).val = (coord t).hom (AddMonoidAlgebra.single x 1) := rfl

theorem exists_coord_eq (φ : torusRing ZU X ⟶ Γ(Z.left, ⊤)) :
    ∃ t : Z ⟶ splitTorus S X, coord t = φ := by
  refine ⟨Over.homMk (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom
    (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), ?_⟩
  have : (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom
    (specULiftZIsTerminal.hom_ext _ _) : Z.left ⟶ (splitTorus S X).left) ≫ torusFst S X =
      Z.left.toSpecΓ ≫ Spec.map φ := pullback.lift_fst _ _ _
  refine (congrArg (fun g => (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ Scheme.Hom.appTop g)
    this).trans ?_
  rw [ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop,
    Iso.inv_hom_id, Category.comp_id]

theorem toHom_bijective : Function.Bijective (toHom : (Z ⟶ splitTorus S X) → _) := by
  constructor
  · intro a b h
    apply coord_injective
    ext1
    refine ringHom_ext_ZU fun y => ?_
    rw [← toHom_val, ← toHom_val, h]
  · intro u
    letI : Algebra (ULift.{0} ℤ) Γ(Z.left, ⊤) := ULift.algebra' ℤ _
    obtain ⟨t, ht⟩ := exists_coord_eq (Z := Z) (X := X) (CommRingCat.ofHom
      (AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u)).toRingHom)
    refine ⟨t, ?_⟩
    ext x
    change (toHom t (Multiplicative.ofAdd x)).val = _
    rw [toHom_val, ht]
    change AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u)
      (AddMonoidAlgebra.single _ 1) = _
    simp

theorem toHom_mul (a b : Z ⟶ splitTorus S X) : toHom (a * b) = toHom a * toHom b := by
  ext x
  exact coord_mul_single a b x

end SplitTorusPoints

noncomputable def splitTorusPointsEquiv (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S) :
    (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ) :=
  { Equiv.ofBijective _ SplitTorusPoints.toHom_bijective with
    map_mul' := SplitTorusPoints.toHom_mul }

theorem splitTorusPointsEquiv_val (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S)
    (t : Z ⟶ splitTorus S X) (χ : X) :
    (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)).val =
      t.left.appTop.hom (charUnit S X χ).val :=
  SplitTorusPoints.coord_single t χ

theorem exists_splitTorus_points_mulEquiv :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S),
      ∃ e : (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ),
        ∀ (t : Z ⟶ splitTorus S X) (χ : X),
          (e t (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val :=
  fun S X _ Z => ⟨splitTorusPointsEquiv S X Z, splitTorusPointsEquiv_val S X Z⟩

end GlobalTheory
