import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

open TensorProduct

noncomputable section

namespace GlobalTheory.TangentCrit

section Alg

variable {R A B k : Type*} [CommRing R] [CommRing A] [CommRing B]

section Der

variable [CommRing k] [Algebra R A] [Algebra A k] [Algebra R k] [IsScalarTower R A k]

def derToDual (D : Derivation R A k) : A →+* DualNumber k where
  toFun a := TrivSqZeroExt.inl (algebraMap A k a) + TrivSqZeroExt.inr (D a)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]

@[simp] lemma fst_derToDual (D : Derivation R A k) (a : A) :
    (derToDual D a).fst = algebraMap A k a := by simp [derToDual]

@[simp] lemma snd_derToDual (D : Derivation R A k) (a : A) :
    (derToDual D a).snd = D a := by simp [derToDual]

def dualToDer (φ : A →+* DualNumber k) (h₁ : ∀ a, (φ a).fst = algebraMap A k a)
    (h₂ : ∀ r, (φ (algebraMap R A r)).snd = 0) : Derivation R A k :=
  Derivation.mk'
    { toFun a := (φ a).snd
      map_add' a b := by simp
      map_smul' r a := by
        rw [Algebra.smul_def, map_mul, DualNumber.snd_mul, h₂, h₁, ← IsScalarTower.algebraMap_apply]
        simp [Algebra.smul_def] }
    (fun a b => by
      simp [h₁, Algebra.smul_def, mul_comm])

@[simp] lemma dualToDer_apply (φ : A →+* DualNumber k) (h₁ : ∀ a, (φ a).fst = algebraMap A k a)
    (h₂ : ∀ r, (φ (algebraMap R A r)).snd = 0) (a : A) :
    dualToDer φ h₁ h₂ a = (φ a).snd := rfl

end Der

lemma lTensor_injective_of_extend {κ M N : Type*} [Field κ] [Field k] [Algebra B κ] [Algebra B k]
    [Algebra κ k] [IsScalarTower B κ k] [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (l : M →ₗ[B] N) (H : ∀ φ : M →ₗ[B] k, ∃ ψ : N →ₗ[B] k, ψ ∘ₗ l = φ) :
    Function.Injective (l.lTensor κ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [← Module.forall_dual_apply_eq_zero_iff κ]
  intro χ
  obtain ⟨ψ, hψ⟩ := H ((Algebra.linearMap κ k ∘ₗ χ).restrictScalars B ∘ₗ TensorProduct.mk B κ M 1)
  have : ∀ z : κ ⊗[B] M, ψ.liftBaseChange κ (l.lTensor κ z) = algebraMap κ k (χ z) := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c m =>
      have h := LinearMap.congr_fun hψ m
      simp only [LinearMap.comp_apply] at h
      have e : c ⊗ₜ[B] m = c • ((1 : κ) ⊗ₜ[B] m) := by simp [smul_tmul']
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, h, e, map_smul]
      simp [Algebra.smul_def]
  have h := this z
  rw [hz, map_zero] at h
  exact (algebraMap κ k).injective (by rw [← h, map_zero])

lemma formallySmooth_of_split [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallySmooth R B] (r : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R])
    (hr : r ∘ₗ KaehlerDifferential.mapBaseChange R A B = LinearMap.id) :
    Algebra.FormallySmooth A B := by
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R A B) :=
    Function.LeftInverse.injective (g := r) (LinearMap.congr_fun hr)
  rw [Algebra.formallySmooth_iff]
  constructor
  · have hex := KaehlerDifferential.exact_mapBaseChange_map R A B
    have hs := KaehlerDifferential.map_surjective R A B
    have h₀ : ∃ l, l ∘ₗ KaehlerDifferential.mapBaseChange R A B = LinearMap.id := ⟨r, hr⟩
    obtain ⟨s, hs'⟩ : ∃ l, KaehlerDifferential.map R A B B ∘ₗ l = LinearMap.id :=
      ((hex.split_tfae hinj hs).out 1 0).mp h₀
    exact Module.Projective.of_split s _ hs'
  · refine subsingleton_of_forall_eq 0 fun x => ?_
    have h₁ : Algebra.H1Cotangent.δ R A B x = 0 := by
      apply hinj
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B).apply_apply_eq_zero x
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R A B x).mp h₁
    rw [Subsingleton.elim y 0, map_zero]

theorem formallySmooth_of_dual_lift [Field k] [IsLocalRing B] (α : R →+* A) (β : A →+* B)
    (hA : α.EssFiniteType) (hB : (β.comp α).EssFiniteType) (hs : (β.comp α).FormallySmooth)
    (x : B →+* k) [IsLocalHom x]
    (H : ∀ ψ : A →+* DualNumber k, (∀ a, (ψ a).fst = x (β a)) → (∀ r, (ψ (α r)).snd = 0) →
      ∃ φ : B →+* DualNumber k, (∀ b, (φ b).fst = x b) ∧ ∀ a, φ (β a) = ψ a) :
    β.FormallySmooth := by
  algebraize [α, β, β.comp α, x, x.comp β, (x.comp β).comp α]
  have : IsScalarTower R B k := .of_algebraMap_eq' rfl
  haveI : IsLocalHom (algebraMap B k) := ‹_›
  letI : Algebra (IsLocalRing.ResidueField B) k := (IsLocalRing.ResidueField.lift x).toAlgebra
  haveI : IsScalarTower B (IsLocalRing.ResidueField B) k := .of_algebraMap_eq fun _ => rfl
  haveI : Module.Free B Ω[B⁄R] := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (KaehlerDifferential.mapBaseChange R A B)).mpr (lTensor_injective_of_extend (k := k) _ fun χ => by
      let D : Derivation R A k :=
        ((χ.restrictScalars A) ∘ₗ TensorProduct.mk A B Ω[A⁄R] 1).compDer (KaehlerDifferential.D R A)
      obtain ⟨φ, h₁, h₂⟩ := H (derToDual D) (fun a => fst_derToDual D a)
        (fun r => (snd_derToDual D _).trans (D.map_algebraMap r))
      let E : Derivation R B k := dualToDer φ h₁ (fun r => by
        change (φ (β (α r))).snd = 0
        rw [h₂]; exact (snd_derToDual D _).trans (D.map_algebraMap r))
      refine ⟨E.liftKaehlerDifferential, ?_⟩
      refine TensorProduct.AlgebraTensorModule.curry_injective (LinearMap.ext_ring ?_)
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)
      have : E (algebraMap A B a) = D a := by
        change (φ (β a)).snd = _
        rw [h₂, snd_derToDual]
      simpa [D, KaehlerDifferential.map_D] using this)
  exact formallySmooth_of_split r hr

theorem formallyUnramified_of_dual_const.{u} {A B : Type u} [CommRing A] [CommRing B]
    (β : A →+* B) (hβ : β.EssFiniteType)
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (φ : B →+* DualNumber k),
      (∀ a, (φ (β a)).snd = 0) → ∀ b, (φ b).snd = 0) : β.FormallyUnramified := by
  algebraize [β]
  refine ⟨?_⟩
  rw [← Module.support_eq_empty_iff (R := B), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  let κ := p.asIdeal.ResidueField
  let k := AlgebraicClosure κ
  have key : Function.Injective ((0 : Ω[B⁄A] →ₗ[B] PUnit.{1}).lTensor κ) :=
    lTensor_injective_of_extend (k := k) _ fun χ => by
      refine ⟨0, ?_⟩
      let D : Derivation A B k := χ.compDer (KaehlerDifferential.D A B)
      have := H k (derToDual D) (fun a => (snd_derToDual D _).trans (D.map_algebraMap a))
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
      have := this b
      rw [snd_derToDual] at this
      simpa [D] using this.symm
  obtain ⟨z, hz⟩ := exists_ne (0 : κ ⊗[B] Ω[B⁄A])
  exact hz (key (by simp))

end Alg

section Sch

open AlgebraicGeometry CategoryTheory Limits

universe u

abbrev dualPt (k : Type u) [CommRing k] : Spec (.of k) ⟶ Spec (.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

abbrev dualBase (k : Type u) [CommRing k] : Spec (.of (DualNumber k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

@[reassoc]
lemma dualPt_dualBase (k : Type u) [CommRing k] : dualPt k ≫ dualBase k = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

theorem formallyUnramified_of_tangent {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (w : Spec (.of (DualNumber k)) ⟶ X),
      w ≫ f = dualBase k ≫ dualPt k ≫ w ≫ f → w = dualBase k ≫ dualPt k ≫ w) :
    FormallyUnramified f := by
  refine ⟨fun {U} hU {V} hV e => formallyUnramified_of_dual_const _
    (f.finiteType_appLE hU hV e).essFiniteType fun k _ _ φ hφ b => ?_⟩
  have := H k (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) (by
    simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV e, ← Spec.map_comp_assoc]
    congr 2
    ext a
    · rfl
    · exact hφ a)
  simp only [← Spec.map_comp_assoc] at this
  rw [cancel_mono, Spec.map_inj] at this
  exact congrArg TrivSqZeroExt.snd congr($this b)

theorem locallyOfFinitePresentation_of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ π)] [LocallyOfFiniteType π] :
    LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).1]
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π (f x))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW : U ≤ π ⁻¹ᵁ W⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxW (π ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, RingHom.FinitePresentation.of_comp_finiteType
    (π.appLE W U hUW).hom ?_ (π.finiteType_appLE hW hU hUW)⟩
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  exact (f ≫ π).finitePresentation_appLE hW hV _

theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  refine ⟨fun {U} hU {V} hV e => ?_⟩
  have h₁ := f.formallyUnramified_appLE hU hV e
  have h₂ := f.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

theorem hom_ext_of_ker_inf {D E₁ E₂ : CommRingCat.{u}} (p₁ : D ⟶ E₁) (p₂ : D ⟶ E₂)
    (hs : Function.Surjective (Spec.map p₁)) (h : ∀ d, p₁ d = 0 → p₂ d = 0 → d = 0)
    {X : Scheme.{u}} {g g' : Spec D ⟶ X} (h₁ : Spec.map p₁ ≫ g = Spec.map p₁ ≫ g')
    (h₂ : Spec.map p₂ ≫ g = Spec.map p₂ ≫ g') : g = g' := by
  have hsurj : Function.Surjective (equalizer.ι g g') := by
    intro y
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨equalizer.lift _ h₁ z, by rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩
  have : IsClosedImmersion (equalizer.ι g g') :=
    .of_isPreimmersion _ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have key : ∀ {E : CommRingCat.{u}} (p : D ⟶ E) (_ : Spec.map p ≫ g = Spec.map p ≫ g')
      (d : Γ(Spec D, ⊤)), (equalizer.ι g g').appTop d = 0 → p ((Scheme.ΓSpecIso D).hom d) = 0 := by
    intro E p hp d hd
    have e : (Spec.map p).appTop d = 0 := by
      rw [← equalizer.lift_ι _ hp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hd, map_zero]
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, e, map_zero]
  have : IsIso (equalizer.ι g g') := by
    refine IsClosedImmersion.isIso_of_injective_of_isAffine ((injective_iff_map_eq_zero _).mpr ?_)
    intro d hd
    apply (Scheme.ΓSpecIso D).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact h _ (key p₁ h₁ d hd) (key p₂ h₂ d hd)
  rw [← cancel_epi (equalizer.ι g g'), equalizer.condition]

lemma SpecMap_fromSpecStalk_closedPoint {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by
  exact (Scheme.Hom.comp_apply _ _ _).trans
    ((congrArg (X.fromSpecStalk x) Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)

theorem smooth_of_tangent {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) [Smooth (f ≫ π)]
    [LocallyOfFiniteType π]
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
      (v : Spec (.of (DualNumber k)) ⟶ Y), dualPt k ≫ v = x ≫ f → v ≫ π = dualBase k ≫ x ≫ f ≫ π →
      ∃ w : Spec (.of (DualNumber k)) ⟶ X, dualPt k ≫ w = x ∧ w ≫ f = v) :
    Smooth f := by
  have := locallyOfFinitePresentation_of_comp f π
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro x -
  let k := AlgebraicClosure (IsLocalRing.ResidueField (X.presheaf.stalk x))
  let ξ : X.presheaf.stalk x →+* k := (algebraMap _ k).comp (IsLocalRing.residue _)
  have hξ : IsLocalHom ξ := inferInstance
  have e : (f.stalkMap x).hom.comp (π.stalkMap (f x)).hom = ((f ≫ π).stalkMap x).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  refine formallySmooth_of_dual_lift (π.stalkMap (f x)).hom (f.stalkMap x).hom
    (LocallyOfFiniteType.stalkMap π _) (e ▸ LocallyOfFiniteType.stalkMap (f ≫ π) x)
    (e ▸ (f ≫ π).smoothLocus_eq_top.ge (Set.mem_univ x)) ξ fun ψ h₁ h₂ => ?_
  obtain ⟨w, hw₁, hw₂⟩ := H k (Spec.map (CommRingCat.ofHom ξ) ≫ X.fromSpecStalk x)
    (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk (f x)) (by
      simp only [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
      congr 2
      ext a
      exact h₁ a) (by
      rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc,
        ← Scheme.SpecMap_stalkMap_fromSpecStalk]
      simp only [← Spec.map_comp_assoc]
      congr 2
      ext a
      · exact h₁ _
      · exact h₂ a)
  obtain ⟨⟨y, φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (.of (DualNumber k))).symm.surjective w
  change _ ≫ Spec.map φ ≫ X.fromSpecStalk y = _ at hw₁
  change (Spec.map φ ≫ X.fromSpecStalk y) ≫ f = _ at hw₂
  rw [← Spec.map_comp_assoc] at hw₁
  obtain rfl : y = x := by
    have h₃ : IsLocalHom (CommRingCat.ofHom ξ).hom := hξ
    have h₄ : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom).hom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
    have h₅ : IsLocalHom (φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom).hom :=
      RingHom.isLocalHom_comp _ _
    exact (SpecMap_fromSpecStalk_closedPoint _).symm.trans
      ((congrArg (fun g : Spec (.of k) ⟶ X => g (IsLocalRing.closedPoint k)) hw₁).trans
        (SpecMap_fromSpecStalk_closedPoint _))
  rw [cancel_mono, Spec.map_inj] at hw₁
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc, cancel_mono,
    Spec.map_inj] at hw₂
  exact ⟨φ.hom, fun b => congr($hw₁ b), fun a => congr($hw₂ a)⟩

end Sch

end GlobalTheory.TangentCrit

namespace GlobalTheory.GrpTangent

section Grp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit

section Ring

variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H]

def epsZero (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (dualPt R) (dualPt_dualBase R)

def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])

@[simp] lemma epsScale_left (c : R) : (epsScale c).left = spMap (epsScaleR c) := rfl

lemma isTangent_iff (w : epsR R ⟶ G) : IsTangent w ↔ epsZero R ≫ w = 1 := by
  rw [← one_eq_one]
  exact ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg Over.Hom.left h⟩

lemma isTangent_comp {w : epsR R ⟶ G} (hw : IsTangent w) (f : G ⟶ H) [IsMonHom f] :
    IsTangent (w ≫ f) := by
  rw [isTangent_iff] at hw ⊢
  rw [← Category.assoc, hw, one_comp]

def tangentMap (f : G ⟶ H) [IsMonHom f] (w : {w : epsR R ⟶ G // IsTangent w}) :
    {w : epsR R ⟶ H // IsTangent w} := ⟨w.1 ≫ f, isTangent_comp w.2 f⟩

@[simp] lemma tangentMap_coe (f : G ⟶ H) [IsMonHom f] (w : {w : epsR R ⟶ G // IsTangent w}) :
    (tangentMap f w).1 = w.1 ≫ f := rfl

@[reassoc]
lemma epsZero_epsScale (c : R) : epsZero R ≫ epsScale c = epsZero R := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp [epsScaleR]

@[reassoc]
lemma epsScale_mul (a b : R) : epsScale a ≫ epsScale b = epsScale (a * b) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR, _root_.mul_assoc]

lemma epsScale_one : epsScale (1 : R) = 𝟙 _ := by
  ext1
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR]

lemma epsScale_zero : epsScale (0 : R) = toUnit _ ≫ epsZero R := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

lemma isTangent_epsScale (c : R) {w : epsR R ⟶ G} (hw : IsTangent w) :
    IsTangent (epsScale c ≫ w) := by
  rw [isTangent_iff] at hw ⊢
  rw [epsZero_epsScale_assoc, hw]

lemma epsScale_zero_comp {w : epsR R ⟶ G} (hw : IsTangent w) : epsScale 0 ≫ w = 1 := by
  rw [epsScale_zero, Category.assoc, (isTangent_iff w).mp hw, comp_one]

def sqZeroMap {M N : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N] (l : M →ₗ[R] N) :
    Over.mk (spMap (algebraMap R (TrivSqZeroExt R N))) ⟶
      Over.mk (spMap (algebraMap R (TrivSqZeroExt R M))) :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (TrivSqZeroExt.map l).comp_algebraMap)

lemma sqZeroMap_comp_eq {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] (l : R →ₗ[R] M) (l' : M →ₗ[R] R) :
    sqZeroMap l' ≫ sqZeroMap l = epsScale (l' (l 1)) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [epsScaleR, this]

theorem epsScale_add_comp (a b : R) {w : epsR R ⟶ G} (hw : IsTangent w) :
    epsScale (a + b) ≫ w = (epsScale a ≫ w) * (epsScale b ≫ w) := by
  let i₁ := LinearMap.inl R R R
  let i₂ := LinearMap.inr R R R
  have key : sqZeroMap (i₁ + i₂) ≫ w = (sqZeroMap i₁ ≫ w) * (sqZeroMap i₂ ≫ w) := by
    ext1
    refine hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMap (LinearMap.fst R R R) ≫ _ = sqZeroMap (LinearMap.fst R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMap_comp_eq]
      simp [i₁, i₂, epsScale_zero_comp hw]
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMap (LinearMap.snd R R R) ≫ _ = sqZeroMap (LinearMap.snd R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMap_comp_eq]
      simp [i₁, i₂, epsScale_zero_comp hw]
  have := congrArg (sqZeroMap (a • LinearMap.fst R R R + b • LinearMap.snd R R R) ≫ ·) key
  simp only [comp_mul, ← Category.assoc, sqZeroMap_comp_eq] at this
  simpa [i₁, i₂] using this

theorem pow_eq_epsScale_comp {w : epsR R ⟶ G} (hw : IsTangent w) (n : ℕ) :
    w ^ n = epsScale (n : R) ≫ w := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, epsScale_zero_comp hw]
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, epsScale_add_comp _ _ hw, ih, epsScale_one, Category.id_comp]

end Ring

section Base

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]

theorem mulN_eq_pow (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = 𝟙 G ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem comp_mulN {T : Over S} (x : T ⟶ G) (n : ℕ) : x ≫ mulN G n = x ^ n := by
  rw [mulN_eq_pow, comp_pow, Category.comp_id]

instance isMonHom_mulN (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom (mulN G n) where
  one_hom := by rw [comp_mulN, one_eq_one, one_pow]
  mul_hom := by
    rw [comp_mulN, mul_eq_mul, comp_mul, mul_pow]
    congr 1 <;> simp [comp_mulN]

theorem pullback_map_mulN {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (n : ℕ) :
    (Over.pullback p).map (mulN G n) = mulN ((Over.pullback p).obj G) n := by
  rw [mulN_eq_pow, mulN_eq_pow, ← (Over.pullback p).map_id]
  exact map_pow (Over.pullback p).homMonoidHom _ _

@[reassoc]
lemma one_pullback_left_fst {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    η[(Over.pullback p).obj G].left ≫ pullback.fst G.hom p = p ≫ η[G].left := by
  rw [Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

section Field

variable {k : Type} [CommRing k] (p : Sp k ⟶ S)

def toFibre {X : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) : epsR k ⟶ (Over.pullback p).obj X :=
  Over.homMk (pullback.lift w.left (dualBase k) (Over.w w)) (pullback.lift_snd _ _ _)

@[reassoc]
lemma toFibre_left_fst {X : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) :
    (toFibre p w).left ≫ pullback.fst X.hom p = w.left := pullback.lift_fst _ _ _

lemma toFibre_injective {X : Over S} : Function.Injective (toFibre p (X := X)) := fun w w' h =>
  Over.OverMorphism.ext (by rw [← toFibre_left_fst, h, toFibre_left_fst])

lemma toFibre_surjective {X : Over S} : Function.Surjective (toFibre p (X := X)) := fun w =>
  ⟨Over.homMk (w.left ≫ pullback.fst X.hom p) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ p) (Over.w w)),
    Over.OverMorphism.ext (pullback.hom_ext (toFibre_left_fst p _)
      ((Over.w _).trans (Over.w w).symm))⟩

lemma toFibre_comp {X Y : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) (f : X ⟶ Y) :
    toFibre p (w ≫ f) = toFibre p w ≫ (Over.pullback p).map f := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have : ((Over.pullback p).map f).left ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ f.left :=
    pullback.lift_fst _ _ _
  rw [toFibre_left_fst, Over.comp_left, Over.comp_left, Category.assoc, this,
    toFibre_left_fst_assoc]

def epsZeroAt : Over.mk p ⟶ Over.mk (dualBase k ≫ p) :=
  Over.homMk (dualPt k) (by simp [dualPt_dualBase_assoc])

def epsBaseAt : Over.mk (dualBase k ≫ p) ⟶ Over.mk p := Over.homMk (dualBase k) rfl

@[reassoc]
lemma epsZeroAt_epsBaseAt : epsZeroAt p ≫ epsBaseAt p = 𝟙 _ :=
  Over.OverMorphism.ext (dualPt_dualBase k)

lemma isTangent_toFibre (w : Over.mk (dualBase k ≫ p) ⟶ G) :
    IsTangent (toFibre p w) ↔ epsZeroAt p ≫ w = 1 := by
  have e : (1 : Over.mk p ⟶ G).left = p ≫ η[G].left := by
    rw [Hom.one_def, Over.comp_left]; rfl
  constructor
  · intro h
    refine Over.OverMorphism.ext ?_
    rw [e, ← one_pullback_left_fst, ← h, Category.assoc, toFibre_left_fst]
    rfl
  · intro h
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, toFibre_left_fst, one_pullback_left_fst, ← e, ← h]
      rfl
    · rw [Category.assoc]
      exact ((congrArg (dualPt k ≫ ·) (Over.w (toFibre p w))).trans (dualPt_dualBase k)).trans
        (Over.w η[(Over.pullback p).obj G]).symm

variable (f : G ⟶ H) [IsMonHom f]

lemma exists_lift_of_tangentMap_surjective
    (h : Function.Surjective (tangentMap ((Over.pullback p).map f))) (x : Over.mk p ⟶ G)
    (v : Over.mk (dualBase k ≫ p) ⟶ H) (hv : epsZeroAt p ≫ v = x ≫ f) :
    ∃ w : Over.mk (dualBase k ≫ p) ⟶ G, epsZeroAt p ≫ w = x ∧ w ≫ f = v := by
  obtain ⟨⟨w, hw⟩, e⟩ := h ⟨toFibre p (v * (epsBaseAt p ≫ x ≫ f)⁻¹), (isTangent_toFibre p _).mpr (by
    rw [comp_mul, GrpObj.comp_inv, epsZeroAt_epsBaseAt_assoc, hv, mul_inv_cancel])⟩
  obtain ⟨w, rfl⟩ := toFibre_surjective p w
  have e' : w ≫ f = v * (epsBaseAt p ≫ x ≫ f)⁻¹ :=
    toFibre_injective p ((toFibre_comp p w f).trans (congrArg Subtype.val e))
  refine ⟨w * (epsBaseAt p ≫ x), ?_, ?_⟩
  · rw [comp_mul, (isTangent_toFibre p w).mp hw, epsZeroAt_epsBaseAt_assoc, _root_.one_mul]
  · rw [mul_comp, e', Category.assoc, inv_mul_cancel_right]

lemma eq_of_tangentMap_injective
    (h : Function.Injective (tangentMap ((Over.pullback p).map f)))
    (w w' : Over.mk (dualBase k ≫ p) ⟶ G) (h₀ : epsZeroAt p ≫ w = epsZeroAt p ≫ w')
    (hf : w ≫ f = w' ≫ f) : w = w' := by
  have := @h ⟨toFibre p (w * w'⁻¹), (isTangent_toFibre p _).mpr (by
      rw [comp_mul, GrpObj.comp_inv, h₀, mul_inv_cancel])⟩
    ⟨toFibre p 1, (isTangent_toFibre p _).mpr (comp_one _)⟩ (Subtype.ext (by
      simp only [tangentMap_coe, ← toFibre_comp]
      rw [mul_comp, GrpObj.inv_comp, hf, mul_inv_cancel, one_comp]))
  exact mul_inv_eq_one.mp (toFibre_injective p (congrArg Subtype.val this))

end Field

theorem formallyUnramified_of_tangentMap_injective (f : G ⟶ H) [IsMonHom f]
    [LocallyOfFiniteType f.left]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Injective (tangentMap ((Over.pullback p).map f))) :
    FormallyUnramified f.left := by
  refine formallyUnramified_of_tangent _ fun k _ _ w hw => ?_
  let p : Sp k ⟶ S := dualPt k ≫ w ≫ G.hom
  have hw' : w ≫ G.hom = dualBase k ≫ p := by
    have := congrArg (· ≫ H.hom) hw
    simpa [p] using this
  let w₀ : Over.mk (dualBase k ≫ p) ⟶ G := Over.homMk w hw'
  exact congrArg Over.Hom.left (eq_of_tangentMap_injective p f (h k p) w₀
    (epsBaseAt p ≫ epsZeroAt p ≫ w₀) (by rw [epsZeroAt_epsBaseAt_assoc])
    (Over.OverMorphism.ext (by simpa [w₀, epsBaseAt, epsZeroAt] using hw)))

theorem smooth_of_tangentMap_surjective (f : G ⟶ H) [IsMonHom f] [Smooth G.hom]
    [LocallyOfFiniteType H.hom]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Surjective (tangentMap ((Over.pullback p).map f))) :
    Smooth f.left := by
  have : Smooth (f.left ≫ H.hom) := by rw [Over.w]; infer_instance
  refine smooth_of_tangent f.left H.hom fun k _ _ x v h₁ h₂ => ?_
  let p : Sp k ⟶ S := x ≫ f.left ≫ H.hom
  obtain ⟨w, hw₁, hw₂⟩ := exists_lift_of_tangentMap_surjective p f (h k p)
    (Over.homMk x (by simp [p])) (Over.homMk v h₂) (Over.OverMorphism.ext h₁)
  exact ⟨w.left, congrArg Over.Hom.left hw₁, congrArg Over.Hom.left hw₂⟩

theorem etale_of_tangentMap_bijective (f : G ⟶ H) [IsMonHom f] [Smooth G.hom]
    [LocallyOfFiniteType H.hom]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Bijective (tangentMap ((Over.pullback p).map f))) :
    Etale f.left := by
  have := smooth_of_tangentMap_surjective f fun k _ _ p => (h k p).2
  have := formallyUnramified_of_tangentMap_injective f fun k _ _ p => (h k p).1
  exact Etale.of_formallyUnramified_of_flat _

end Base

section MulN

theorem comp_mulN_left_of_isTangent {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]
    {w : epsR R ⟶ G} (hw : IsTangent w) (n : ℕ) :
    (w ≫ mulN G n).left = spMap (epsScaleR (n : R)) ≫ w.left := by
  rw [comp_mulN, pow_eq_epsScale_comp hw]; rfl

theorem tangentMap_mulN_bijective {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] {n : ℕ} (hn : IsUnit (n : R)) : Function.Bijective (tangentMap (mulN G n)) := by
  obtain ⟨u, hu⟩ := hn
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun w => ⟨epsScale (↑u⁻¹ : R) ≫ w.1, isTangent_epsScale _ w.2⟩, fun w => Subtype.ext ?_,
      fun w => Subtype.ext ?_⟩
  · simp only [tangentMap_coe]
    rw [comp_mulN, pow_eq_epsScale_comp w.2, epsScale_mul_assoc, ← hu, Units.inv_mul, epsScale_one,
      Category.id_comp]
  · simp only [tangentMap_coe]
    rw [comp_mulN, pow_eq_epsScale_comp (isTangent_epsScale _ w.2), epsScale_mul_assoc, ← hu,
      Units.mul_inv, epsScale_one, Category.id_comp]

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

lemma isUnit_natCast_of_point {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) {R : Type} [CommRing R]
    (p : Sp R ⟶ S) : IsUnit (n : R) := by
  simpa using hn.map (p.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom).hom

lemma tangentMap_pullback_mulN_bijective [IsCommMonObj G] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    {R : Type} [CommRing R] (p : Sp R ⟶ S) :
    Function.Bijective (tangentMap ((Over.pullback p).map (mulN G n))) := by
  convert tangentMap_mulN_bijective ((Over.pullback p).obj G) (isUnit_natCast_of_point hn p) using 2
  exact pullback_map_mulN p G n

theorem formallyUnramified_mulN [IsCommMonObj G] [LocallyOfFiniteType G.hom] {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulN G n).left := by
  have : LocallyOfFiniteType ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have := locallyOfFiniteType_of_comp (mulN G n).left G.hom
  exact formallyUnramified_of_tangentMap_injective _ fun k _ _ p =>
    (tangentMap_pullback_mulN_bijective G hn p).1

theorem etale_mulN [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    Etale (mulN G n).left :=
  etale_of_tangentMap_bijective _ fun _ _ _ p => tangentMap_pullback_mulN_bijective G hn p

theorem etale_id_pow [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    Etale (𝟙 G ^ n).left := mulN_eq_pow G n ▸ etale_mulN G hn

theorem isPullback_torsion (n : ℕ) :
    IsPullback (torsion.ι G n).left (torsion G n).hom (mulN G n).left η[G].left := by
  have h := (IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).left = (torsion G n).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h

theorem etale_torsion [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    Etale (torsion G n).hom :=
  MorphismProperty.of_isPullback (P := @Etale) (isPullback_torsion G n) (etale_mulN G hn)

theorem isFinite_mulN [IsCommMonObj G] [Smooth G.hom] [IsProper G.hom] {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) : IsFinite (mulN G n).left := by
  have := etale_mulN G hn
  have : IsProper ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have := IsProper.of_comp (mulN G n).left G.hom
  have := locallyQuasiFinite_of_formallyUnramified (mulN G n).left
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem isFinite_id_pow [IsCommMonObj G] [Smooth G.hom] [IsProper G.hom] {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) : IsFinite (𝟙 G ^ n).left := mulN_eq_pow G n ▸ isFinite_mulN G hn

theorem isFinite_torsion [IsCommMonObj G] [Smooth G.hom] [IsProper G.hom] {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) : IsFinite (torsion G n).hom :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_torsion G n) (isFinite_mulN G hn)

theorem finiteEtale_mulN_torsion [hG : IsAbelianScheme G] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    (IsFinite (mulN G n).left ∧ Etale (mulN G n).left) ∧
      IsFinite (torsion G n).hom ∧ Etale (torsion G n).hom :=
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  ⟨⟨isFinite_mulN G hn, etale_mulN G hn⟩, isFinite_torsion G hn, etale_torsion G hn⟩

end MulN

theorem etale_hom_and_mulN :
    (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] [Smooth G.hom] [Smooth H.hom]
      (f : G ⟶ H) [IsMonHom f],
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
        Function.Bijective (tangentMap ((Over.pullback p).map f))) → Etale f.left) ∧
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
        Function.Injective (tangentMap ((Over.pullback p).map f))) → FormallyUnramified f.left) ∧
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
        Function.Surjective (tangentMap ((Over.pullback p).map f))) → Smooth f.left)) ∧
    (∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (n : ℕ) (w : epsR R ⟶ G),
      IsTangent w → (w ≫ mulN G n).left = spMap (epsScaleR (n : R)) ≫ w.left) ∧
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (n : ℕ),
      IsUnit (n : Γ(S, ⊤)) → Etale (mulN G n).left ∧ Etale (torsion G n).hom) ∧
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsAbelianScheme G] (n : ℕ),
      IsUnit (n : Γ(S, ⊤)) → (IsFinite (mulN G n).left ∧ Etale (mulN G n).left) ∧
        IsFinite (torsion G n).hom ∧ Etale (torsion G n).hom) := by
  refine ⟨fun S G H _ _ _ _ f _ => ⟨etale_of_tangentMap_bijective f, fun h => ?_,
      smooth_of_tangentMap_surjective f⟩,
    fun R _ G _ n w hw => comp_mulN_left_of_isTangent hw n,
    fun S G _ _ _ n hn => ⟨etale_mulN G hn, etale_torsion G hn⟩,
    fun S G _ _ n hn => finiteEtale_mulN_torsion G hn⟩
  have : LocallyOfFiniteType (f.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have := locallyOfFiniteType_of_comp f.left H.hom
  exact formallyUnramified_of_tangentMap_injective f h

end Grp

end GlobalTheory.GrpTangent
