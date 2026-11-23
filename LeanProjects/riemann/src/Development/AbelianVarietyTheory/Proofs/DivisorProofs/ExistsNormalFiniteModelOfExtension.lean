import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalizationRelativeDimZero

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BplusDescent

section Field

variable {X : Scheme.{0}} [IsIntegral X] {L : Type} [Field L] (φ : X.presheaf.stalk (genericPoint X) ⟶ .of L)

abbrev fieldPt : Spec (.of L) ⟶ X := Spec.map φ ≫ X.fromSpecStalk (genericPoint X)

theorem fieldPt_apply (x : Spec (.of L)) : fieldPt φ x = genericPoint X := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  have : Spec.map φ x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
  change X.fromSpecStalk _ (Spec.map φ x) = _
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

theorem top_le_fieldPt {U : X.Opens} (hU : genericPoint X ∈ U) : ⊤ ≤ fieldPt φ ⁻¹ᵁ U := fun x _ => by
  change fieldPt φ x ∈ U
  rwa [fieldPt_apply]

theorem fieldPt_appLE {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) ≫ (Scheme.ΓSpecIso (.of L)).hom = X.presheaf.germ U _ hU ≫ φ := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U := fun x _ => by
    letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    have : x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
    change X.fromSpecStalk _ x ∈ U
    rw [this, Scheme.fromSpecStalk_closedPoint]
    exact hU
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) (X.fromSpecStalk (genericPoint X)) U ⊤ ⊤ h1 le_rfl]
  have h2 : (Spec.map φ).appLE ⊤ ⊤ le_rfl = (Spec.map φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [h2, Category.assoc, Scheme.ΓSpecIso_naturality, Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  have h3 : ∀ i : (Opposite.op ⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opensᵒᵖ) ⟶ Opposite.op ⊤,
      (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map i = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
  rw [h3]
  simp

def normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    Γ((fieldPt φ).normalization, (fieldPt φ).fromNormalization ⁻¹ᵁ U) ⟶ .of L :=
  (fieldPt φ).toNormalization.appLE _ ⊤ (by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU) ≫
    (Scheme.ΓSpecIso (.of L)).hom

theorem app_normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).fromNormalization.app U ≫ normFun φ hU = X.presheaf.germ U _ hU ≫ φ := by
  have key : ∀ (g : Spec (.of L) ⟶ X) (_ : g = fieldPt φ) (e : ⊤ ≤ g ⁻¹ᵁ U),
      g.appLE U ⊤ e = (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) := by
    rintro _ rfl _
    rfl
  rw [normFun, ← fieldPt_appLE, ← Category.assoc]
  congr 1
  exact (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans (key _ (fieldPt φ).toNormalization_fromNormalization (by
    rw [Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU))

theorem map_normFun {U U' : X.Opens} (hU : genericPoint X ∈ U) (hU' : genericPoint X ∈ U') (h : U' ≤ U) :
    (fieldPt φ).normalization.presheaf.map (homOfLE ((fieldPt φ).fromNormalization.preimage_mono h)).op ≫
      normFun φ hU' = normFun φ hU := by
  rw [normFun, normFun, Scheme.Hom.map_appLE_assoc]

theorem normFun_spec {U : X.Opens} (hU : genericPoint X ∈ U) (hA : IsAffineOpen U) :
    Function.Injective (normFun φ hU).hom ∧
      ∀ x : L, x ∈ (normFun φ hU).hom.range ↔ (X.presheaf.germ U _ hU ≫ φ).hom.IsIntegralElem x := by
  let u := fieldPt φ
  letI := (u.app U).hom.toAlgebra
  let ε : Γ(Spec (.of L), u ⁻¹ᵁ U) ⟶ .of L :=
    (Spec (.of L)).presheaf.map (homOfLE (top_le_fieldPt φ hU)).op ≫ (Scheme.ΓSpecIso (.of L)).hom
  have hε : Function.Bijective ε.hom := by
    have : homOfLE (top_le_fieldPt φ hU) = eqToHom (top_le_iff.1 (top_le_fieldPt φ hU)).symm := Subsingleton.elim _ _
    haveI : IsIso ε := by
      simp only [ε, this]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ε
  have h1 : normFun φ hU = (u.normalizationObjIso hA).hom ≫
      CommRingCat.ofHom (integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U)).val.toRingHom ≫ ε := by
    rw [← Category.assoc, u.normalizationObjIso_hom_val hA, normFun]
    simp only [ε]
    rw [Scheme.Hom.appLE_map_assoc]
  have h2 : X.presheaf.germ U _ hU ≫ φ = u.app U ≫ ε := by
    rw [← fieldPt_appLE, Scheme.Hom.appLE, Category.assoc]
  have hb := ConcreteCategory.bijective_of_isIso (u.normalizationObjIso hA).hom
  rw [h1, h2]
  refine ⟨hε.1.comp (Subtype.val_injective.comp hb.1), fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨p, hp, hp0⟩ := ((u.normalizationObjIso hA).hom y).2
    refine ⟨p, hp, ?_⟩
    have := congrArg ε.hom hp0
    rw [Polynomial.hom_eval₂, map_zero] at this
    exact this
  · rintro ⟨p, hp, hp0⟩
    obtain ⟨y, rfl⟩ := hε.2 x
    have hy : IsIntegral Γ(X, U) y := ⟨p, hp, hε.1 (by rw [Polynomial.hom_eval₂, map_zero]; exact hp0)⟩
    obtain ⟨z, hz⟩ := hb.2 ⟨y, hy⟩
    exact ⟨z, congrArg (fun w : integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U) => ε.hom w.1) hz⟩

end Field

theorem exists_normalization_in (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (B : GlobalTheory.Vert.Model O) (_ : GlobalTheory.IsNormalScheme B.X) (K' : IntermediateField B.X.functionField (Kbar B.X))
    (hK : FiniteDimensional B.X.functionField K') :
    ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (γ : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp),
      GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ IsFinite f.f ∧ (∀ U, Function.Injective (γ U)) ∧
      (∀ (U : AffOp B.X) (a : Γ(B.X, U.1)), γ U ((f.f.app U.1).hom a) = algebraMap Γ(B.X, U.1) U.Bp a) ∧
      (∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (a : Γ(B'.X, f.f ⁻¹ᵁ U.1)),
        γ U' ((B'.X.presheaf.map (homOfLE (f.f.preimage_mono hle)).op).hom a) = AffOp.res hle (γ U a)) ∧
      ∀ U, (γ U).range = ringOver K' U := by
  set η := genericPoint B.X
  let ψ : B.X.presheaf.stalk (genericPoint B.X) ⟶ .of K' := CommRingCat.ofHom (algebraMap B.X.functionField K')
  let u : Spec (.of K') ⟶ B.X := fieldPt ψ
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ B.str)
  have hu : u (IsLocalRing.closedPoint K') = η := fieldPt_apply ψ _
  have hφinj : Function.Injective φ.hom := by
    have hη : (B.str η).asIdeal = ⊥ := Model.mem_gen_iff_eq_bot.1 B.genericPoint_mem_gen
    have e : Spec.map φ (IsLocalRing.closedPoint K') = B.str η := by
      rw [hφ]
      exact congrArg B.str hu
    rw [RingHom.injective_iff_ker_eq_bot]
    have e' := congrArg PrimeSpectrum.asIdeal e
    rw [hη] at e'
    rw [← e']
    ext a
    change _ ↔ φ.hom a ∈ IsLocalRing.maximalIdeal K'
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
    rfl
  haveI : CharZero K' := charZero_of_injective_ringHom hφinj
  haveI : LocallyOfFiniteType B.str := inferInstance
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk (o := .of O) B.str η ψ
      (RingHom.finite_algebraMap.2 hK).finiteType.essFiniteType
  let ν := u.fromNormalization
  haveI : Flat (u.fromNormalization ≫ B.str) := by
    have : Flat (u.toNormalization ≫ u.fromNormalization ≫ B.str) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, ← hφ]
      exact Flat.SpecMap_iff.mpr (flat_of_dedekind_of_injective φ.hom hφinj)
    exact flat_normalization u _
  let B' : Model O :=
    { X := u.normalization
      str := ν ≫ B.str
      isIntegral := inferInstance
      isProjOver := isProjOver_comp_of_isFinite ν B.isProjOver
      flat := ‹_› }
  have hrange : Set.range ν = Set.univ := by
    have hcl : IsClosed (Set.range ν) := ν.isClosedMap.isClosed_range
    have hmem : η ∈ Set.range ν :=
      ⟨u.toNormalization (IsLocalRing.closedPoint K'), by
        change (u.toNormalization ≫ u.fromNormalization) _ = η
        rw [Scheme.Hom.toNormalization_fromNormalization]
        exact hu⟩
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec B.X).def]
    exact hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
  haveI : Surjective ν := ⟨fun x => hrange.ge (Set.mem_univ x)⟩
  let n : Model.Hom B' B := ⟨ν, rfl⟩
  have hx : ∀ U : AffOp B.X, genericPoint B.X ∈ U.1 := fun U =>
    ((genericPoint_spec B.X).mem_open_set_iff U.1.isOpen).2 (by simpa using U.2.2)
  have hint : ∀ (U : AffOp B.X) (x : K'), (B.X.presheaf.germ U.1 _ (hx U) ≫ ψ).hom.IsIntegralElem x ↔
      IsIntegral Γ(B.X, U.1) (x : Kbar B.X) := fun U x => by
    refine exists_congr fun p => and_congr_right fun _ => ?_
    rw [← (map_eq_zero_iff K'.val.toRingHom Subtype.val_injective), Polynomial.hom_eval₂]
    rfl
  let γ : ∀ U : AffOp B.X, Γ(B'.X, n.f ⁻¹ᵁ U.1) →+* U.Bp := fun U =>
    (K'.val.toRingHom.comp (normFun ψ (hx U)).hom).codRestrict (integralClosure Γ(B.X, U.1) (Kbar B.X)) fun a =>
      (hint U _).1 (((normFun_spec ψ (hx U) U.2.1).2 _).1 ⟨a, rfl⟩)
  refine ⟨B', n, γ, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u, ?_, hfin, fun U a b h => ?_, fun U a => ?_,
    fun U U' hle a => ?_, fun U => ?_⟩
  · have hdim := Model.topologicalKrullDim_genFibre O B B' n
    haveI : Subsingleton n.genFibre := by
      constructor
      intro a b
      have key : ∀ c : n.genFibre, (ν.fiberι η) c = genericPoint B'.X := fun c => by
        have hc : (ν.fiberι η) c ∈ ν ⁻¹' {η} := by
          rw [← Scheme.Hom.range_fiberι]; exact ⟨c, rfl⟩
        exact Model.eq_genericPoint_of_isFinite ν hc
      exact (ν.fiberι η).isEmbedding.injective ((key a).trans (key b).symm)
    have h0 := topologicalKrullDim_zero_of_discreteTopology n.genFibre
    rw [hdim] at h0
    have h1 : n.relDim ≤ 0 := by exact_mod_cast h0
    omega
  · exact (normFun_spec ψ (hx U) U.2.1).1 (Subtype.ext (congrArg (fun z : U.Bp => (z : Kbar B.X)) h))
  · exact Subtype.ext (congrArg (fun g : Γ(B.X, U.1) ⟶ .of K' => (g.hom a : Kbar B.X)) (app_normFun ψ (hx U)))
  · exact Subtype.ext (congrArg (fun g : Γ(B'.X, n.f ⁻¹ᵁ U.1) ⟶ .of K' => (g.hom a : Kbar B.X))
      (map_normFun ψ (hx U) (hx U') hle))
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ((normFun ψ (hx U)).hom a).2
    · intro h
      obtain ⟨a, ha⟩ := ((normFun_spec ψ (hx U) U.2.1).2 ⟨x.1, h⟩).2 ((hint U _).2 x.2)
      exact ⟨a, Subtype.ext (congrArg (fun z : K' => (z : Kbar B.X)) ha)⟩

end GlobalTheory.BplusDescent

end
