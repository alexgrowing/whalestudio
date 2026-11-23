import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieInh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem stdSmooth_mvPolynomial (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  have hker : (Algebra.Generators.mvPolynomial R (Fin n)).ker = ⊥ := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val, Algebra.Generators.mvPolynomial_val]
    exact (RingHom.injective_iff_ker_eq_bot _).1 fun a b h => by
      simpa only [MvPolynomial.aeval_X_left_apply] using h
  let P : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨Algebra.Generators.mvPolynomial R (Fin n), Empty.elim, by rw [hker]; simp⟩
  let P' : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P, Empty.elim, fun a => a.elim⟩
  let P'' : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P', by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty, map_one]
      exact isUnit_one⟩
  refine Algebra.IsStandardSmoothOfRelativeDimension.mk ⟨Fin n, Empty, inferInstance, inferInstance, P'', ?_⟩
  simp [Algebra.Presentation.dimension]

theorem smooth_affineSpace (S : Scheme.{0}) (n : ℕ) :
    SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
  have hZ : SmoothOfRelativeDimension n (𝔸(Fin n; Spec (CommRingCat.of ℤ)) ↘ Spec (CommRingCat.of ℤ)) := by
    have e : (𝔸(Fin n; Spec (CommRingCat.of ℤ)) ↘ Spec (CommRingCat.of ℤ)) =
        (AffineSpace.SpecIso (Fin n) (CommRingCat.of ℤ)).hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
      rw [← AffineSpace.SpecIso_inv_over, Iso.hom_inv_id_assoc]
    rw [e, MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension n),
      HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2 (stdSmooth_mvPolynomial ℤ n))
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n)
    (AffineSpace.isPullback_map (n := Fin n)
      (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom (S.presheaf.obj (Opposite.op ⊤)))))) hZ

def gaFunctor (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Multiplicative Γ(T.unop.left, ⊤))
  map g := GrpCat.ofHom (MonoidHom.mk' (fun v => Multiplicative.ofAdd (g.unop.left.appTop.hom v.toAdd))
    fun v w => map_add g.unop.left.appTop.hom v.toAdd w.toAdd)
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun v =>
    congrArg (fun q => q.hom v.toAdd) (Scheme.Hom.id_appTop (X := T.unop.left)))
  map_comp g g' := GrpCat.hom_ext (MonoidHom.ext fun x => rfl)

def gaObj (X : Scheme.{0}) : Over X := Over.mk (𝔸(Fin 1; X) ↘ X)

def gaEquiv {X : Scheme.{0}} (T : Over X) :
    (T ⟶ gaObj X) ≃ Multiplicative Γ(T.left, ⊤) where
  toFun x := Multiplicative.ofAdd (x.left.appTop (AffineSpace.coord X 0))
  invFun v := Over.homMk (AffineSpace.homOfVector T.hom fun _ => v.toAdd) (AffineSpace.homOfVector_over _ _)
  left_inv x := Over.OverMorphism.ext (AffineSpace.hom_ext
    ((AffineSpace.homOfVector_over _ _).trans (Over.w x).symm) fun i => by
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact AffineSpace.homOfVector_appTop_coord _ _ _)
  right_inv v := AffineSpace.homOfVector_appTop_coord T.hom (fun _ : Fin 1 => v.toAdd) 0

def gaRep (X : Scheme.{0}) : (gaFunctor X ⋙ forget _).RepresentableBy (gaObj X) where
  homEquiv {T} := gaEquiv T
  homEquiv_comp _ _ := rfl

instance (X : Scheme.{0}) : GrpObj (gaObj X) := GrpObj.ofRepresentableBy _ _ (gaRep X)

theorem gaEquiv_mul {X : Scheme.{0}} {T : Over X} (x y : T ⟶ gaObj X) :
    gaEquiv T (x * y) = gaEquiv T x * gaEquiv T y := by
  have hcomp : ∀ {T' : Over X} (f : T ⟶ T') (g : T' ⟶ gaObj X),
      gaEquiv T (f ≫ g) = ((gaFunctor X).map f.op).hom (gaEquiv T' g) := fun _ _ => rfl
  have hμ : gaEquiv (gaObj X ⊗ gaObj X) MonObj.mul =
      gaEquiv _ (fst (gaObj X) (gaObj X)) * gaEquiv _ (snd (gaObj X) (gaObj X)) := by
    erw [MonObj.ofRepresentableBy_mul]
    exact Equiv.apply_symm_apply _ _
  rw [Hom.mul_def, hcomp, hμ, map_mul, ← hcomp, ← hcomp, lift_fst, lift_snd]

theorem gaEquiv_one {X : Scheme.{0}} {T : Over X} :
    gaEquiv T (1 : T ⟶ gaObj X) = 1 := by
  have hcomp : ∀ {T' : Over X} (f : T ⟶ T') (g : T' ⟶ gaObj X),
      gaEquiv T (f ≫ g) = ((gaFunctor X).map f.op).hom (gaEquiv T' g) := fun _ _ => rfl
  have h1 : gaEquiv (𝟙_ (Over X)) MonObj.one = 1 := by
    erw [MonObj.ofRepresentableBy_one]
    exact Equiv.apply_symm_apply _ _
  rw [Hom.one_def, hcomp, h1, map_one]

instance (X : Scheme.{0}) : IsCommMonObj (gaObj X) where
  mul_comm := by
    have h : fst (gaObj X) (gaObj X) * snd (gaObj X) (gaObj X) =
        snd (gaObj X) (gaObj X) * fst (gaObj X) (gaObj X) :=
      (gaEquiv _).injective (by rw [gaEquiv_mul, gaEquiv_mul, _root_.mul_comm])
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [← lift_snd_fst]
    exact h.symm

variable {X : Scheme.{0}}

def gaPt {A : Type} [CommRing A] (y : Spec (CommRingCat.of A) ⟶ X) (a : A) : Over.mk y ⟶ gaObj X :=
  (gaEquiv (Over.mk y)).symm (Multiplicative.ofAdd ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))

theorem gaPt_add {A : Type} [CommRing A] (y : Spec (CommRingCat.of A) ⟶ X) (a b : A) :
    gaPt y (a + b) = gaPt y a * gaPt y b := by
  have e : ∀ c : A, gaEquiv (Over.mk y) (gaPt y c) =
      Multiplicative.ofAdd ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) :=
    fun c => (gaEquiv _).apply_symm_apply _
  apply (gaEquiv (Over.mk y)).injective
  rw [gaEquiv_mul, e, e, e, map_add, ofAdd_add]

theorem gaPt_zero {A : Type} [CommRing A] (y : Spec (CommRingCat.of A) ⟶ X) : gaPt y 0 = 1 := by
  have e : ∀ c : A, gaEquiv (Over.mk y) (gaPt y c) =
      Multiplicative.ofAdd ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) :=
    fun c => (gaEquiv _).apply_symm_apply _
  apply (gaEquiv (Over.mk y)).injective
  rw [gaEquiv_one, e, map_zero, ofAdd_zero]

theorem gaPt_bijective {A : Type} [CommRing A] (y : Spec (CommRingCat.of A) ⟶ X) :
    Function.Bijective (gaPt y) := by
  have e : ∀ c : A, gaEquiv (Over.mk y) (gaPt y c) =
      Multiplicative.ofAdd ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) :=
    fun c => (gaEquiv _).apply_symm_apply _
  refine Function.bijective_iff_has_inverse.2
    ⟨fun v => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaEquiv (Over.mk y) v).toAdd, fun c => ?_, fun v => ?_⟩
  · show (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaEquiv (Over.mk y) (gaPt y c)).toAdd = c
    rw [e]
    exact Iso.inv_hom_id_apply _ _
  · apply (gaEquiv (Over.mk y)).injective
    show gaEquiv (Over.mk y) (gaPt y ((Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaEquiv (Over.mk y) v).toAdd)) = _
    rw [e, Iso.hom_inv_id_apply]
    rfl

theorem map_gaPt {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (y : Spec (CommRingCat.of A) ⟶ X) (z : Spec (CommRingCat.of B) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ y = z) (a : A) :
    Spec.map (CommRingCat.ofHom φ) ≫ (gaPt y a).left = (gaPt z (φ a)).left := by
  subst h
  have e2 : ∀ {A' : Type} [CommRing A'] (y' : Spec (CommRingCat.of A') ⟶ X) (c : A'),
      (gaPt y' c).left.appTop (AffineSpace.coord X 0) = (Scheme.ΓSpecIso (CommRingCat.of A')).inv c :=
    fun y' c => congrArg Multiplicative.toAdd ((gaEquiv (Over.mk y')).apply_symm_apply _)
  have w1 : ∀ {A' : Type} [CommRing A'] (y' : Spec (CommRingCat.of A') ⟶ X) (c : A'),
      (gaPt y' c).left ≫ (𝔸(Fin 1; X) ↘ X) = y' := fun y' c => Over.w (gaPt y' c)
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, w1, w1]
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
    exact (congrArg (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ))).hom (e2 y a)).trans
      (((congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm).trans
        (e2 _ (φ a)).symm)

variable {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)

theorem map_base (φ : DualNumber R →+* R) (h : φ.comp (algebraMap R (DualNumber R)) = RingHom.id R) :
    Spec.map (CommRingCat.ofHom φ) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = x := by
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

theorem isTanAt_gaPt (a : DualNumber R) :
    IsTanAt (gaObj X) x (gaPt _ a) ↔ a.fst = 0 := by
  show (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (gaPt _ a).left =
      (1 : Over.mk x ⟶ gaObj X).left) ↔ a.fst = 0
  have hb : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = x :=
    map_base x _ (RingHom.ext fun _ => rfl)
  rw [map_gaPt _ _ x hb a, ← gaPt_zero x]
  constructor
  · intro h
    exact (gaPt_bijective x).1 (Over.OverMorphism.ext h)
  · intro h
    rw [show (TrivSqZeroExt.fstHom R R R).toRingHom a = 0 from h]

def gaLie : LieModel (gaObj X) x R where
  pt r := gaPt _ (TrivSqZeroExt.inr r : DualNumber R)
  tan r := (isTanAt_gaPt x _).2 rfl
  inj r s h := TrivSqZeroExt.inr_injective ((gaPt_bijective _).1 h)
  onto v hv := by
    obtain ⟨a, rfl⟩ := (gaPt_bijective _).2 v
    refine ⟨a.snd, congrArg (gaPt _) ?_⟩
    have := (isTanAt_gaPt x a).1 hv
    ext <;> simp [this]
  add r s := by rw [TrivSqZeroExt.inr_add, gaPt_add]
  smul c r := by
    rw [map_gaPt (epsMul c) _ (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)]
    · congr 2
      ext <;> simp [epsMul, _root_.mul_comm]
    · rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
      congr 3
      ext <;> simp [epsMul]

end GlobalTheory.CompanionTheory.Ar.LieInh

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem exists_lieModel_line :
    ∃ (G : Over (Spec (CommRingCat.of ℤ))) (_ : GrpObj G) (_ : IsCommMonObj G),
      SmoothOfRelativeDimension 1 G.hom ∧ ∀ (R : Type) [CommRing R]
        (x : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℤ)), Nonempty (LieModel G x R) := by
  exact ⟨LieInh.gaObj _, inferInstance, inferInstance, LieInh.smooth_affineSpace _ 1, fun R _ x => ⟨LieInh.gaLie x⟩⟩

end GlobalTheory.CompanionTheory.Ar
