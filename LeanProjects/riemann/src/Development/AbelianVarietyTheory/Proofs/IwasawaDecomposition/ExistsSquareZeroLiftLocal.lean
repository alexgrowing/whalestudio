import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpUniqCh0.SqZeroFactor

theorem comp_one_over {X : Scheme.{0}} {Y Z M : Over X} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit Z) (toUnit Y)]

theorem specMap_stalkCongr_fromSpecStalk {Y : Scheme.{0}} {x y : Y} (h : x = y) :
    Spec.map (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Y.fromSpecStalk x = Y.fromSpecStalk y := by
  subst h
  simp

theorem isLocalHom_of_field {S R : Type} [Field S] [CommRing R] [Nontrivial R] (f : S →+* R) : IsLocalHom f := by
  constructor
  intro a ha
  by_cases h : a = 0
  · subst h
    rw [map_zero] at ha
    exact absurd ha not_isUnit_zero
  · exact Ne.isUnit h

section Ring

variable {S A B : Type} [Field S] [CommRing A] [Algebra S A] [IsLocalRing A] [CommRing B] [Algebra S B]
  [IsLocalRing B] (q : A →ₐ[S] B) [Module Sᵐᵒᵖ (RingHom.ker q)] [IsCentralScalar S (RingHom.ker q)]
  (hJ : RingHom.ker q ^ 2 = ⊥)

theorem incl_injective : Function.Injective (incl (S := S) (RingHom.ker q) hJ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [incl_apply] at hx
  have h1 : x.fst = 0 := by
    by_contra h
    have hu : IsUnit (algebraMap S A x.fst) := (Ne.isUnit h).map _
    have hj : ((x.snd : A)) = -(algebraMap S A x.fst) := eq_neg_of_add_eq_zero_right hx
    have hmem : ((x.snd : A)) ∈ RingHom.ker q := x.snd.2
    rw [hj] at hmem
    exact RingHom.ker_ne_top q (Ideal.eq_top_of_isUnit_mem _ hmem hu.neg)
  have h2 : (x.snd : A) = 0 := by rw [h1, map_zero, zero_add] at hx; exact hx
  exact TrivSqZeroExt.ext (by simpa using h1) (by simpa using Subtype.ext h2)

variable {R : Type} [CommRing R] (φ : R →+* A) (ψ : R →+* S) (h : ∀ f, q (φ f) = algebraMap S B (ψ f))

def liftFun (f : R) : TrivSqZeroExt S (RingHom.ker q) :=
  (ψ f, ⟨φ f - algebraMap S A (ψ f), RingHom.mem_ker.2 (by rw [map_sub, h, AlgHom.commutes, sub_self])⟩)

theorem incl_liftFun (f : R) : incl (S := S) (RingHom.ker q) hJ (liftFun q φ ψ h f) = φ f := by
  rw [incl_apply]
  show algebraMap S A (ψ f) + (φ f - algebraMap S A (ψ f)) = φ f
  ring

def lift (hJ : RingHom.ker q ^ 2 = ⊥) : R →+* TrivSqZeroExt S (RingHom.ker q) where
  toFun := liftFun q φ ψ h
  map_one' := incl_injective q hJ (by rw [incl_liftFun q hJ, map_one, map_one])
  map_mul' x y := incl_injective q hJ (by rw [map_mul, incl_liftFun q hJ, incl_liftFun q hJ, incl_liftFun q hJ, map_mul])
  map_zero' := incl_injective q hJ (by rw [incl_liftFun q hJ, map_zero, map_zero])
  map_add' x y := incl_injective q hJ (by rw [map_add, incl_liftFun q hJ, incl_liftFun q hJ, incl_liftFun q hJ, map_add])

theorem incl_comp_lift : (incl (S := S) (RingHom.ker q) hJ : TrivSqZeroExt S (RingHom.ker q) →+* A).comp (lift q φ ψ h hJ) = φ :=
  RingHom.ext fun f => incl_liftFun q hJ φ ψ h f

theorem fst_comp_lift : (TrivSqZeroExt.fstHom S S (RingHom.ker q) : TrivSqZeroExt S (RingHom.ker q) →+* S).comp (lift q φ ψ h hJ) = ψ :=
  RingHom.ext fun _ => rfl

end Ring

end GlobalTheory.ExpUniqCh0.SqZeroFactor

open GlobalTheory.ExpUniqCh0.SqZeroFactor in

theorem GlobalTheory.ExpUniqCh0.exists_factor_trivSqZeroExt : ∀ {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [Field S] (x0 : Sp S ⟶ X)
    {A B : Type} [CommRing A] [Algebra S A] [IsLocalRing A] [CommRing B] [Algebra S B] [IsLocalRing B]
    (q : A →ₐ[S] B), Function.Surjective q → ∀ [Module Sᵐᵒᵖ (RingHom.ker q)] [IsCentralScalar S (RingHom.ker q)]
    (hJ : RingHom.ker q ^ 2 = ⊥) (δ : overAt x0 A ⟶ G), Formalism.L2.Pj.homAt x0 q ≫ δ = 1 →
    ∃ ε : overAt x0 (TrivSqZeroExt S (RingHom.ker q)) ⟶ G,
      Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.fstHom S S (RingHom.ker q)) ≫ ε = 1 ∧ Formalism.L2.Pj.homAt x0 (incl (RingHom.ker q) hJ) ≫ ε = δ := by
  intro X G _ S _ x0 A B _ _ _ _ _ _ q hq _ _ hJ δ hδ
  let u : Sp S ⟶ G.left := (1 : overAt x0 S ⟶ G).left
  have hδ' : spMap (q : A →+* B) ≫ δ.left = spMap (algebraMap S B) ≫ u := by
    have h1 : (1 : overAt x0 B ⟶ G) = homAt x0 (Algebra.ofId S B) ≫ 1 := (comp_one_over _).symm
    have h2 := congrArg (fun f => f.left) (hδ.trans h1)
    exact h2
  haveI : IsLocalHom (q : A →+* B) := IsLocalHom.of_surjective _ hq
  haveI : IsLocalHom (algebraMap S B) := isLocalHom_of_field _
  haveI : IsLocalHom (algebraMap S A) := isLocalHom_of_field _
  let φ := Scheme.stalkClosedPointTo δ.left
  have hδl : Spec.map φ ≫ G.left.fromSpecStalk _ = δ.left := Scheme.Spec_stalkClosedPointTo_fromSpecStalk δ.left
  let φ₁ := Scheme.stalkClosedPointTo u
  have hu : Spec.map φ₁ ≫ G.left.fromSpecStalk _ = u := Scheme.Spec_stalkClosedPointTo_fromSpecStalk u
  have l1 : IsLocalHom (φ ≫ CommRingCat.ofHom (q : A →+* B)).hom := by
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
  have l2 : IsLocalHom (φ₁ ≫ CommRingCat.ofHom (algebraMap S B)).hom := by
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
  have e1 : (SpecToEquivOfLocalRing G.left (CommRingCat.of B)).symm ⟨_, φ ≫ CommRingCat.ofHom (q : A →+* B), l1⟩ =
      (SpecToEquivOfLocalRing G.left (CommRingCat.of B)).symm ⟨_, φ₁ ≫ CommRingCat.ofHom (algebraMap S B), l2⟩ := by
    rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply, Spec.map_comp, Spec.map_comp,
      Category.assoc, Category.assoc, hδl, hu]
    exact hδ'
  obtain ⟨hp, hφ⟩ := SpecToEquivOfLocalRing_eq_iff.mp ((SpecToEquivOfLocalRing _ _).symm.injective e1)
  let ψc := (G.left.presheaf.stalkCongr (Inseparable.of_eq hp)).hom ≫ φ₁
  have hψu : Spec.map ψc ≫ G.left.fromSpecStalk _ = u := by
    rw [Spec.map_comp, Category.assoc, specMap_stalkCongr_fromSpecStalk hp, hu]
  have hψ : ∀ f, q (φ.hom f) = algebraMap S B (ψc.hom f) := fun f => by
    have := congrArg (fun g => g.hom f) hφ
    simpa [ψc] using this

  let φε := lift q φ.hom ψc.hom hψ hJ
  let εl : Sp (TrivSqZeroExt S (RingHom.ker q)) ⟶ G.left := Spec.map (CommRingCat.ofHom φε) ≫ G.left.fromSpecStalk _
  let m := G.hom.stalkMap (δ.left (IsLocalRing.closedPoint A))
  have key : ∀ {R : CommRingCat} (g : G.left.presheaf.stalk (δ.left (IsLocalRing.closedPoint A)) ⟶ R),
      Spec.map g ≫ G.left.fromSpecStalk _ ≫ G.hom = Spec.map (m ≫ g) ≫ X.fromSpecStalk _ := by
    intro R g
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc]
  have hx0 : Spec.map (m ≫ ψc) ≫ X.fromSpecStalk _ = x0 := by
    rw [← key, ← Category.assoc, hψu]
    have hw := Over.w (1 : overAt x0 S ⟶ G)
    refine hw.trans ?_
    show spMap (algebraMap S S) ≫ x0 = x0
    rw [Algebra.algebraMap_self]
    simp [spMap]
  have hδx : Spec.map (m ≫ φ) ≫ X.fromSpecStalk _ = Spec.map (m ≫ ψc ≫ CommRingCat.ofHom (algebraMap S A)) ≫ X.fromSpecStalk _ := by
    rw [← key, ← Category.assoc, hδl, Over.w δ]
    show spMap (algebraMap S A) ≫ x0 = _
    conv_lhs => rw [← hx0]
    rw [← Category.assoc, ← Spec.map_comp]
    simp [spMap]

  haveI : IsLocalHom (G.left.presheaf.stalkCongr (Inseparable.of_eq hp)).hom.hom := isLocalHom_of_isIso _
  haveI : IsLocalHom m.hom := inferInstanceAs (IsLocalHom (G.hom.stalkMap (δ.left (IsLocalRing.closedPoint A))).hom)
  haveI : IsLocalHom φ.hom := Scheme.isLocalHom_stalkClosedPointTo _
  haveI : IsLocalHom φ₁.hom := Scheme.isLocalHom_stalkClosedPointTo _
  have l3 : IsLocalHom (m ≫ φ).hom := CommRingCat.isLocalHom_comp _ _
  have l4 : IsLocalHom (m ≫ ψc ≫ CommRingCat.ofHom (algebraMap S A)).hom := by
    haveI : IsLocalHom ψc.hom := CommRingCat.isLocalHom_comp _ _
    haveI : IsLocalHom (CommRingCat.ofHom (algebraMap S A)).hom := by rw [CommRingCat.hom_ofHom]; infer_instance
    haveI : IsLocalHom (ψc ≫ CommRingCat.ofHom (algebraMap S A)).hom := CommRingCat.isLocalHom_comp _ _
    exact CommRingCat.isLocalHom_comp _ _
  have e2 : (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm ⟨_, m ≫ φ, l3⟩ =
      (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm ⟨_, m ≫ ψc ≫ CommRingCat.ofHom (algebraMap S A), l4⟩ := by
    rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
    exact hδx
  obtain ⟨hxx, hmφ⟩ := SpecToEquivOfLocalRing_eq_iff.mp ((SpecToEquivOfLocalRing _ _).symm.injective e2)
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at hmφ
  have hmε : m ≫ CommRingCat.ofHom φε = m ≫ ψc ≫ CommRingCat.ofHom (algebraMap S (TrivSqZeroExt S (RingHom.ker q))) := by
    refine CommRingCat.hom_ext (RingHom.ext fun g => ?_)
    apply incl_injective q hJ
    have := congrArg (fun k => k.hom g) hmφ
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this ⊢
    rw [AlgHom.commutes]
    exact (incl_liftFun q hJ φ.hom ψc.hom hψ _).trans this

  have hover : εl ≫ G.hom = (overAt x0 (TrivSqZeroExt S (RingHom.ker q))).hom := by
    show Spec.map (CommRingCat.ofHom φε) ≫ G.left.fromSpecStalk _ ≫ G.hom = spMap _ ≫ x0
    rw [key]
    erw [hmε]
    conv_rhs => rw [← hx0]
    simp only [spMap, Spec.map_comp, Category.assoc]
  refine ⟨Over.homMk εl hover, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    show spMap _ ≫ Spec.map (CommRingCat.ofHom φε) ≫ G.left.fromSpecStalk _ = u
    rw [← hψu, ← Category.assoc, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_comp_lift q hJ φ.hom ψc.hom hψ,
      CommRingCat.ofHom_hom]
  · apply Over.OverMorphism.ext
    show spMap _ ≫ Spec.map (CommRingCat.ofHom φε) ≫ G.left.fromSpecStalk _ = δ.left
    rw [← Category.assoc, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, incl_comp_lift q hJ φ.hom ψc.hom hψ,
      CommRingCat.ofHom_hom, hδl]
