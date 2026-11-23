import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.UnifBaseChangeInjOfSeamsCS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.UBC

open Semi

section Adj

theorem homEquiv_mul {S S' : Scheme.{0}} (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : (Over.map φ).obj X ⟶ A) :
    (Over.mapPullbackAdj φ).homEquiv X A (a * b) =
      (Over.mapPullbackAdj φ).homEquiv X A a * (Over.mapPullbackAdj φ).homEquiv X A b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

theorem homEquiv_one {S S' : Scheme.{0}} (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A] :
    (Over.mapPullbackAdj φ).homEquiv X A 1 = 1 := by
  rw [Adjunction.homEquiv_unit, Functor.map_one, MonObj.comp_one]

theorem toBase_eq_symm {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) (T : Over S')
    (x : T ⟶ (Over.pullback f).obj A) :
    toBase (pullback.condition : pullback.fst A.hom f ≫ A.hom = pullback.snd A.hom f ≫ f) x =
      ((Over.mapPullbackAdj f).homEquiv T A).symm x := by
  rfl

theorem eps_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) :
    (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.fst (𝟙_ (Over S)).hom f = f := by
  have h1 : (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.snd (𝟙_ (Over S)).hom f =
      𝟙 S' :=
    Over.w (Functor.LaxMonoidal.ε (Over.pullback f))
  have h2 : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f :=
    (Category.comp_id _).symm.trans pullback.condition
  rw [h2, ← Category.assoc, h1]
  exact Category.id_comp f

theorem eSec_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A] :
    eSec ((Over.pullback f).obj A) ≫ pullback.fst A.hom f = f ≫ eSec A := by
  simp only [eSec, Functor.obj.η_def, Over.comp_left, Category.assoc]
  erw [pullback.lift_fst]
  rw [← Category.assoc, eps_pullback_fst f]

theorem inv_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A] :
    (ι[(Over.pullback f).obj A]).left ≫ pullback.fst A.hom f = pullback.fst A.hom f ≫ (ι[A]).left := by
  simp [Functor.obj.ι_def]
  exact pullback.lift_fst _ _ _

end Adj

def PolPullSt : Prop :=
  ∀ (R : Type) [CommRing R] (S' : Scheme.{0}) (f : S' ⟶ Spec (CommRingCat.of R))
    (P : PolAV (Spec (CommRingCat.of R))),
    Rigidified ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f)) ∧
    Sym ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f)) ∧
    RelAmple ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f)) ∧
    KTriv ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f))

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

abbrev pA (φ : R →+* R') (A : Over (Spec (CommRingCat.of R))) : Over (Spec (CommRingCat.of R')) :=
  (Over.pullback (specOf φ)).obj A

abbrev pF (φ : R →+* R') (A : Over (Spec (CommRingCat.of R))) : (pA φ A).left ⟶ A.left :=
  (Iso.refl (pA φ A)).hom.left ≫ pullback.fst A.hom (specOf φ)

lemma pF_eq (φ : R →+* R') (A : Over (Spec (CommRingCat.of R))) :
    pF φ A = pullback.fst A.hom (specOf φ) := by
  simp [pF]

def pullPol (φ : R →+* R') (P : PolAV (Spec (CommRingCat.of R))) [hP : Fact PolPullSt] :
    PolAV (Spec (CommRingCat.of R')) where
  A := pA φ P.A
  isAb := TLinPf.isAb_pullback _ P.A P.isAb
  g := P.g
  smoothDim := by
    show SmoothOfRelativeDimension P.g (pullback.snd P.A.hom (specOf φ))
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := P.g)
    first
      | exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P.g)
          (IsPullback.of_hasPullback P.A.hom (specOf φ)) P.smoothDim
      | exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P.g)
          (IsPullback.of_hasPullback P.A.hom (specOf φ)).flip P.smoothDim
  L := P.L.pull (pF φ P.A)
  isLB := Semi.LB.isLB_pull P.isLB _
  rigid := by rw [pF_eq]; exact (hP.out R (Spec (CommRingCat.of R')) (specOf φ) P).1
  sym := by rw [pF_eq]; exact (hP.out R (Spec (CommRingCat.of R')) (specOf φ) P).2.1
  ample := by rw [pF_eq]; exact (hP.out R (Spec (CommRingCat.of R')) (specOf φ) P).2.2.1
  ktriv := by rw [pF_eq]; exact (hP.out R (Spec (CommRingCat.of R')) (specOf φ) P).2.2.2

def pc (φ : R →+* R') {A : Over (Spec (CommRingCat.of R))}
    (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A) : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ pA φ A :=
  (Over.mapPullbackAdj (specOf φ)).homEquiv _ _ (toUnit _ ≫ x)

lemma pc_pr (φ : R →+* R') {A : Over (Spec (CommRingCat.of R))}
    (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A) :
    (pc φ x).left ≫ pF φ A = specOf φ ≫ x.left := by
  rw [pF_eq]
  have hsymm : (((Over.mapPullbackAdj (specOf φ)).homEquiv _ A).symm (pc φ x)).left =
      (pc φ x).left ≫ pullback.fst A.hom (specOf φ) := rfl
  rw [← hsymm]
  simp only [pc, Equiv.symm_apply_apply, Over.comp_left]
  congr 1

lemma pc_add (φ : R →+* R') {A : Over (Spec (CommRingCat.of R))} [GrpObj A] [IsCommMonObj A]
    (x y : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A) :
    pc φ (padd A x y) = padd (pA φ A) (pc φ x) (pc φ y) := by
  simp only [pc, padd]
  have key := homEquiv_mul (specOf φ) (𝟙_ (Over (Spec (CommRingCat.of R')))) A
    (toUnit ((Over.map (specOf φ)).obj (𝟙_ (Over (Spec (CommRingCat.of R'))))) ≫ x)
    (toUnit ((Over.map (specOf φ)).obj (𝟙_ (Over (Spec (CommRingCat.of R'))))) ≫ y)
  rw [← MonObj.comp_mul] at key
  exact key

section Kappa

variable (φ : R →+* R') (hφ : Function.Injective φ)

def kap : FractionRing R →+* FractionRing R' :=
  IsLocalization.map (FractionRing R') φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ)

abbrev kapS : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of (FractionRing R)) :=
  Spec.map (CommRingCat.ofHom (kap φ hφ))

lemma kapS_comm : kapS φ hφ ≫ jK R = jK R' ≫ specOf φ := by
  simp only [kapS, jK, specOf, ← Spec.map_comp]
  congr 1
  ext x
  simp [kap, IsLocalization.map_eq]

end Kappa

end ReciprocityTheory.ChartRestriction.G.Out.UBC
