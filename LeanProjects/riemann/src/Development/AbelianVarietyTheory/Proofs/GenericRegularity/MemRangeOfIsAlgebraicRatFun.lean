import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompNonemptyFiniteGenFrTrdeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsOpenImmersionIsStandardSmoothOfRelativeD

namespace GlobalTheory.GeomIrr

section Fields

open Polynomial IntermediateField

theorem natDegree_minpoly_eq {L F Ω : Type*} [Field L] [Field F] [Field Ω] [Algebra L F] [Algebra F Ω]
    [Algebra L Ω] [IsScalarTower L F Ω] (hLF : ∀ x : F, IsIntegral L x → x ∈ (algebraMap L F).range)
    {θ : Ω} (hθ : IsIntegral L θ) : (minpoly F θ).natDegree = (minpoly L θ).natDegree := by
  have hF : IsIntegral F θ := hθ.tower_top
  have hd : minpoly F θ ∣ (minpoly L θ).map (algebraMap L F) := minpoly.dvd_map_of_isScalarTower L F θ
  have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F (minpoly.monic hθ) (minpoly.monic hF) hd
  have h2 : minpoly F θ ∈ lifts (algebraMap L F) := by
    rw [lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨y, hy⟩ := h1 n
    rw [← hy]
    exact hLF _ y.2
  obtain ⟨q, hq, hdeg, hm⟩ := lifts_and_natDegree_eq_and_monic h2 (minpoly.monic hF)
  apply le_antisymm
  · have := natDegree_le_of_dvd hd ((minpoly.monic hθ).map _).ne_zero
    rwa [natDegree_map] at this
  · rw [← hdeg]
    refine natDegree_le_of_dvd (minpoly.dvd L θ ?_) hm.ne_zero
    rw [← aeval_map_algebraMap F, hq, minpoly.aeval]

theorem mem_of_isIntegral {L F Ω : Type*} [Field L] [CharZero L] [Field F] [Field Ω] [Algebra L F] [Algebra F Ω]
    [Algebra L Ω] [IsScalarTower L F Ω] (hLF : ∀ x : F, IsIntegral L x → x ∈ (algebraMap L F).range)
    (M : IntermediateField L Ω) [FiniteDimensional L M] (hgen : adjoin F (M : Set Ω) = ⊤)
    {a : Ω} (ha : IsIntegral L a) : a ∈ M := by
  haveI : FiniteDimensional L L⟮a⟯ := adjoin.finiteDimensional ha
  let N : IntermediateField L Ω := M ⊔ L⟮a⟯
  haveI : FiniteDimensional L N := inferInstance
  have prim : ∀ P : IntermediateField L Ω, FiniteDimensional L P → ∃ θ : Ω, IsIntegral L θ ∧ L⟮θ⟯ = P ∧
      Module.finrank L P = Module.finrank F F⟮θ⟯ := by
    intro P _
    obtain ⟨θ, hθ⟩ := Field.exists_primitive_element L P
    have hi : IsIntegral L (θ : Ω) := (Algebra.IsIntegral.isIntegral (R := L) θ).map P.val
    have e : L⟮(θ : Ω)⟯ = P := by
      have := congrArg (IntermediateField.lift (F := P)) hθ
      simpa using this
    refine ⟨θ, hi, e, ?_⟩
    rw [adjoin.finrank hi.tower_top, natDegree_minpoly_eq hLF hi, ← adjoin.finrank hi, e]
  obtain ⟨θ, hθ, eθ, rθ⟩ := prim M inferInstance
  obtain ⟨η, hη, eη, rη⟩ := prim N inferInstance
  have htop : F⟮θ⟯ = ⊤ := by
    rw [eq_top_iff, ← hgen, adjoin_le_iff, ← eθ]
    have : L⟮θ⟯ ≤ (F⟮θ⟯).restrictScalars L := by
      rw [adjoin_simple_le_iff]
      exact mem_adjoin_simple_self F θ
    exact this
  haveI : FiniteDimensional F F⟮θ⟯ := adjoin.finiteDimensional hθ.tower_top
  have hle : Module.finrank F F⟮η⟯ ≤ Module.finrank F F⟮θ⟯ :=
    IntermediateField.finrank_le_of_le_right (htop ▸ le_top)
  have : M = N := IntermediateField.eq_of_le_of_finrank_le le_sup_left (by omega)
  rw [this]
  exact (le_sup_right : L⟮a⟯ ≤ N) (mem_adjoin_simple_self L a)

theorem mem_range_of_isIntegral {F K Ω : Type*} [Field F] [CharZero F] [Field K] [CharZero K] [Field Ω] [CharZero Ω]
    [FiniteDimensional ℚ K] (φ : F →+* Ω) (ψ : K →+* Ω)
    (hgen : ∀ S : Subfield Ω, (∀ x, φ x ∈ S) → (∀ y, ψ y ∈ S) → S = ⊤)
    (hal : ∀ x : F, IsIntegral ℚ x → φ x ∈ ψ.range) {a : Ω} (ha : IsIntegral ℚ a) : a ∈ ψ.range := by
  letI : Algebra F Ω := φ.toAlgebra
  let L := algebraicClosure ℚ F
  let M : IntermediateField L Ω := ψ.fieldRange.toIntermediateField fun x =>
    hal x (mem_algebraicClosure_iff'.1 x.2)
  haveI : FiniteDimensional ℚ M := by
    let g : K →ₗ[ℚ] M := (ψ.rangeRestrictField : K →+* M).toRatAlgHom.toLinearMap
    exact Module.Finite.of_surjective g ψ.rangeRestrictField_bijective.2
  haveI : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite ℚ L M
  haveI : Algebra.IsIntegral ℚ L := (algebraicClosure.isAlgebraic ℚ F).isIntegral
  refine mem_of_isIntegral (L := L) (F := F) (fun x hx => ?_) M ?_ ha.tower_top
  · exact ⟨⟨x, mem_algebraicClosure_iff'.2 (isIntegral_trans x hx)⟩, rfl⟩
  · have := hgen (adjoin F (M : Set Ω)).toSubfield (fun x => (adjoin F (M : Set Ω)).algebraMap_mem x)
      (fun y => subset_adjoin F _ ⟨y, rfl⟩)
    exact IntermediateField.toSubfield_injective this

theorem mem_range_of_isAlgebraic_ratFun {K σ : Type*} [Field K] (a : FractionRing (MvPolynomial σ K))
    (ha : IsAlgebraic K a) : a ∈ (algebraMap K (FractionRing (MvPolynomial σ K))).range := by
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (ha.isIntegral.tower_top (A := MvPolynomial σ K))
  have hb : IsIntegral K b := (isIntegral_algebraMap_iff (IsFractionRing.injective _ _)).mp ha.isIntegral
  by_cases h0 : b = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨r, -, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 (hb.isUnit h0)
  exact ⟨r, IsScalarTower.algebraMap_apply K (MvPolynomial σ K) _ r⟩

theorem exists_finset_roots (F : Type*) [Field F] [CharZero F] [Algebra.EssFiniteType ℚ F] :
    ∃ s : Finset ℂ, (∀ z ∈ s, IsAlgebraic ℚ z) ∧ ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ s, z ∈ K) →
      ∀ (Ω : Type) [Field Ω] (φ : F →+* Ω) (ψ : K →+* Ω) (x : F), IsIntegral ℚ x → φ x ∈ ψ.range := by
  classical
  let L := algebraicClosure ℚ F
  haveI : FiniteDimensional ℚ L := finiteDimensional_algebraicClosure_of_essFiniteType ℚ F
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ L
  have hi : IsIntegral ℚ θ := Algebra.IsIntegral.isIntegral θ
  let p := minpoly ℚ θ
  refine ⟨(p.aroots ℂ).toFinset, fun z hz => ?_, fun K hK Ω _ φ ψ x hx => ?_⟩
  · rw [Multiset.mem_toFinset, mem_aroots] at hz
    exact ⟨p, hz.1, hz.2⟩
  haveI : CharZero Ω := charZero_of_injective_ringHom φ.injective
  letI : Algebra K Ω := ψ.toAlgebra
  have hs : (p.map (algebraMap ℚ K)).Splits :=
    IntermediateField.splits_of_splits (IsAlgClosed.splits _) fun z hz => hK z (by
      rw [Multiset.mem_toFinset]
      exact Finset.mem_coe.1 hz |> Multiset.mem_toFinset.1)
  let g : L →ₐ[ℚ] Ω := (φ.comp L.val.toRingHom).toRatAlgHom
  have hr : g θ ∈ ψ.range := by
    refine hs.mem_range_of_isRoot (S := Ω) ((minpoly.monic hi).map _).ne_zero ?_
    change (Polynomial.map _ _).IsRoot _
    rw [Polynomial.map_map, Subsingleton.elim (RingHom.comp _ _) (algebraMap ℚ Ω), IsRoot.def, eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hle : (⊤ : IntermediateField ℚ L) ≤ (ψ.toRatAlgHom.fieldRange).comap g := by
    rw [← hθ, adjoin_simple_le_iff]
    exact hr
  exact hle (x := ⟨x, mem_algebraicClosure_iff'.2 hx⟩) trivial

end Fields

section Schemes

open AlgebraicGeometry CategoryTheory Limits

theorem residueField_generated {k K : CommRingCat.{0}} {X : Scheme.{0}} (s : X ⟶ Spec k) (i : k ⟶ K)
    (x : ↥(pullback s (Spec.map i))) (S : Subfield ((pullback s (Spec.map i)).residueField x))
    (h1 : ∀ a, ((pullback.fst s (Spec.map i)).residueFieldMap x).hom a ∈ S)
    (h2 : ∀ a, (Spec.preimage ((pullback s (Spec.map i)).fromSpecResidueField x ≫ pullback.snd _ _)).hom a ∈ S) :
    S = ⊤ := by
  let P := pullback s (Spec.map i)
  let φ : X.residueField (pullback.fst s (Spec.map i) x) ⟶ CommRingCat.of S :=
    CommRingCat.ofHom (((pullback.fst s (Spec.map i)).residueFieldMap x).hom.codRestrict S h1)
  let ψ : K ⟶ CommRingCat.of S :=
    CommRingCat.ofHom ((Spec.preimage (P.fromSpecResidueField x ≫ pullback.snd _ _)).hom.codRestrict S h2)
  let j : CommRingCat.of S ⟶ P.residueField x := CommRingCat.ofHom S.subtype
  have e1 : φ ≫ j = (pullback.fst s (Spec.map i)).residueFieldMap x := rfl
  have e2 : ψ ≫ j = Spec.preimage (P.fromSpecResidueField x ≫ pullback.snd _ _) := rfl
  have f1 : Spec.map j ≫ Spec.map φ ≫ X.fromSpecResidueField _ = P.fromSpecResidueField x ≫ pullback.fst _ _ := by
    rw [← Spec.map_comp_assoc, e1, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have f2 : Spec.map j ≫ Spec.map ψ = P.fromSpecResidueField x ≫ pullback.snd _ _ := by
    rw [← Spec.map_comp, e2, Spec.map_preimage]
  have w : (Spec.map φ ≫ X.fromSpecResidueField _) ≫ s = Spec.map ψ ≫ Spec.map i := by
    obtain ⟨u, hu⟩ := Spec.map_surjective ((Spec.map φ ≫ X.fromSpecResidueField _) ≫ s)
    have h : Spec.map j ≫ Spec.map u = Spec.map j ≫ Spec.map (i ≫ ψ) := by
      rw [hu, Spec.map_comp, reassoc_of% f2, Category.assoc, reassoc_of% f1, pullback.condition]
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
    haveI : Mono j := ConcreteCategory.mono_of_injective j Subtype.val_injective
    rw [← hu, (cancel_mono j).1 h, Spec.map_comp]
  have h : Spec.map j ≫ pullback.lift _ _ w = P.fromSpecResidueField x := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, f1]
    · rw [Category.assoc, pullback.lift_snd, f2]
  haveI : SurjectiveOnStalks (Spec.map j ≫ pullback.lift _ _ w) := by rw [h]; infer_instance
  haveI : SurjectiveOnStalks (Spec.map j) := .of_comp _ (pullback.lift _ _ w)
  have hs : Function.Surjective j.hom :=
    RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 (SurjectiveOnStalks.Spec_iff.1 this)
  rw [eq_top_iff]
  intro a _
  obtain ⟨b, rfl⟩ := hs a
  exact b.2

theorem flat_of_field {A B : Type} [Field A] [CommRing B] (f : A →+* B) : f.Flat := by
  letI := f.toAlgebra
  exact (inferInstance : Module.Flat A B)

theorem apply_mem_genericPoints {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) : f (hZ.1 : IsIrreducible Z).genericPoint ∈ genericPoints Y := by
  have hg := (hZ.1 : IsIrreducible Z).isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hx : ∀ y : X, y ⤳ (hZ.1 : IsIrreducible Z).genericPoint → y = (hZ.1 : IsIrreducible Z).genericPoint := by
    intro y hy
    have h1 : Z ⊆ closure {y} := by
      rw [← hg.def]
      exact specializes_iff_closure_subset.mp hy
    have h2 : closure {y} ⊆ Z := hZ.2 isIrreducible_singleton.closure h1
    exact (hy.antisymm (hg.specializes (h2 (subset_closure rfl)))).eq
  refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
  have hT' := hT.isGenericPoint_genericPoint_closure
  have hs : hT.genericPoint ⤳ f (hZ.1 : IsIrreducible Z).genericPoint :=
    hT'.specializes (subset_closure (hle (subset_closure rfl)))
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap f hs
  rw [← hx y hy, e, hT'.def]
  exact subset_closure

end Schemes

open AlgebraicGeometry CategoryTheory Limits
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem compNe_and_exists_fnAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → CompNe Xo c ∧ ∃ c' : Coeff l, c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → FnAlgClosed Xo c'' := by
  intro E _ _ _ H Dw l Xo c h1
  refine ⟨(GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg E H Dw l Xo c h1).1, ?_⟩
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have : CompactSpace Xo.X := QuasiCompact.compactSpace_of_compactSpace Xo.s
  have : IsNoetherian Xo.X := {}
  have hfin : (genericPoints Xo.X).Finite :=
    genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have := c.fin
  haveI : FiniteDimensional ℚ (KA l) :=
    Module.Finite.of_injective (IntermediateField.inclusion c.le).toLinearMap (IntermediateField.inclusion_injective c.le)
  have hchar : ∀ x : Xo.X, CharZero (Xo.X.residueField x) := fun x =>
    charZero_of_injective_ringHom (R := KA l)
      (Spec.preimage (Xo.X.fromSpecResidueField x ≫ Xo.s)).hom.injective
  have key : ∀ x : Xo.X, ∃ s : Finset ℂ, (∀ z ∈ s, IsAlgebraic ℚ z) ∧ ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ s, z ∈ K) →
      ∀ (Ω : Type) [Field Ω] (φ : Xo.X.residueField x →+* Ω) (ψ : K →+* Ω) (a : Xo.X.residueField x),
        IsIntegral ℚ a → φ a ∈ ψ.range := by
    intro x
    letI : Algebra (KA l) (Xo.X.residueField x) :=
      (Spec.preimage (Xo.X.fromSpecResidueField x ≫ Xo.s)).hom.toAlgebra
    have hess : (Spec.preimage (Xo.X.fromSpecResidueField x ≫ Xo.s)).hom.EssFiniteType := by
      have e : Spec.preimage (Xo.X.fromSpecResidueField x ≫ Xo.s) =
          Spec.preimage ((Sp (KA l)).fromSpecResidueField (Xo.s x)) ≫ Xo.s.residueFieldMap x := by
        rw [← Spec.map_inj]
        simp
      rw [e, CommRingCat.hom_comp]
      refine RingHom.EssFiniteType.comp ?_ (LocallyOfFiniteType.stalkMap Xo.s x).residueFieldMap
      refine (RingHom.FiniteType.of_surjective _ ?_).essFiniteType
      have : SurjectiveOnStalks (Spec.map (Spec.preimage ((Sp (KA l)).fromSpecResidueField (Xo.s x)))) := by
        rw [Spec.map_preimage]; infer_instance
      exact RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 (SurjectiveOnStalks.Spec_iff.1 this)
    haveI : Algebra.EssFiniteType (KA l) (Xo.X.residueField x) := hess
    haveI : Algebra.EssFiniteType ℚ (Xo.X.residueField x) := .comp ℚ (KA l) _
    exact exists_finset_roots _
  choose s hs hK using key
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l
    (hfin.toFinset.biUnion s ∪ Finset.univ.image fun j => (b j : ℂ)) (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.1 h
      exact hs x z hx
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact ((Algebra.IsIntegral.isIntegral (R := ℚ) (b j)).map c.F.val).isAlgebraic)
  refine ⟨c', fun z hz => ?_, fun c'' hle Z a ha => ?_⟩
  · have e := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)
    rw [map_sum] at e
    have e' : z = _ := e.symm
    rw [e']
    refine sum_mem fun j _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _
      (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have := c''.fin
  obtain ⟨r, rfl⟩ := mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c''.F r := (isIntegral_algebraMap_iff (algebraMap (kap Z) (Om Z)).injective).1 ha.isIntegral
  haveI : CharZero (kap Z) := charZero_of_injective_algebraMap (algebraMap c''.F (kap Z)).injective
  have hr' : IsIntegral ℚ r := isIntegral_trans r hr
  let p : Xo.XF c'' ⟶ Xo.X := pullback.fst _ _
  haveI : Flat (spMap (IntermediateField.inclusion c''.le).toRingHom) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact flat_of_field _
  have hp : p (genPt Z) ∈ genericPoints Xo.X := apply_mem_genericPoints p Z.1 Z.2
  obtain ⟨k, hk⟩ := mem_range_of_isIntegral (p.residueFieldMap (genPt Z)).hom (algebraMap c''.F (kap Z))
    (fun S h₁ h₂ => residueField_generated Xo.s _ (genPt Z) S h₁ h₂)
    (hK _ c''.F (fun z hz => hle (hc' z (Finset.mem_union_left _
      (Finset.mem_biUnion.2 ⟨_, hfin.mem_toFinset.2 hp, hz⟩)))) _ _ _) hr'
  exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩

end GlobalTheory.GeomIrr
