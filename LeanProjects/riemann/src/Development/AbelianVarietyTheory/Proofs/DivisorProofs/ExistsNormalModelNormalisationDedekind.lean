import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

set_option maxHeartbeats 1000000 in

theorem exists_ratModel_normalization : ∀ (A o Ω : Type) [CommRing A] [IsDedekindDomain A] [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (κ : A →+* o), κ.Finite → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp A), LocallyOfFiniteType z →
    QuasiCompact z → IsSeparated z → ∀ p : Sp Ω ⟶ Z, p ≫ z = spMap ((algebraMap o Ω).comp κ) →
    (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ (M : RatModel o Ω) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z ∧
    IsFinite π ∧ M.pt ≫ π = p := by
  intro A o Ω _ _ _ _ _ _ κ hκ Z z _ _ _ p hp hfin
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : CharZero (Sp Ω).functionField :=
    charZero_of_injective_ringHom (((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫
      (Sp Ω).germToFunctionField ⊤).hom).injective
  haveI : IsFinite p.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_genericallyFinite (o := CommRingCat.of A) p z hfin
  haveI : GlobalTheory.IsNormalScheme p.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral p
  haveI : IsFinite (spMap κ) := by rw [IsFinite.SpecMap_iff]; exact hκ
  have hl : p ≫ z = spMap (algebraMap o Ω) ≫ spMap κ := by
    rw [hp, ← Spec.map_comp]; rfl
  let l : Sp Ω ⟶ pullback z (spMap κ) := pullback.lift p (spMap (algebraMap o Ω)) hl
  have hl1 : p = l ≫ pullback.fst z (spMap κ) := (pullback.lift_fst _ _ _).symm
  let d := p.normalizationDesc l (pullback.fst z (spMap κ)) hl1
  let s : p.normalization ⟶ Sp o := d ≫ pullback.snd z (spMap κ)
  have hs : s ≫ spMap κ = p.fromNormalization ≫ z := by
    simp only [s, d, Category.assoc, ← pullback.condition]
    rw [Scheme.Hom.normalizationDesc_comp_assoc]
  have hfz : LocallyOfFiniteType (s ≫ spMap κ) ∧ IsSeparated (s ≫ spMap κ) ∧ QuasiCompact (s ≫ spMap κ) := by
    rw [hs]; exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨h1, h2, h3⟩ := hfz
  have hpt_s : p.toNormalization ≫ s = spMap (algebraMap o Ω) := by
    simp only [s, d]
    rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_snd]
  have hgen : Set.range p.toNormalization = {genericPoint p.normalization} := by
    have hr : ∀ w : Sp Ω, w = IsLocalRing.closedPoint Ω := fun w => Subsingleton.elim _ _
    have hrng : Set.range p.toNormalization = {p.toNormalization (IsLocalRing.closedPoint Ω)} :=
      Set.ext fun y => ⟨fun ⟨w, hw⟩ => hw ▸ congrArg p.toNormalization (hr w),
        fun hy => ⟨_, hy.symm⟩⟩
    have : IsGenericPoint (p.toNormalization (IsLocalRing.closedPoint Ω)) (⊤ : Set p.normalization) := by
      rw [isGenericPoint_def, ← hrng]
      exact p.toNormalization.denseRange.closure_range
    rw [hrng, this.eq (genericPoint_spec p.normalization)]
  have honto : ∀ x : Ω, ∃ (U : p.normalization.Opens) (f : Γ(p.normalization, U)), (U : Set p.normalization).Nonempty ∧
      valF p.toNormalization U f = x := by
    intro x
    set ξ : Sp Ω := genericPoint (Sp Ω) with hξ
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := p ξ) (U := ⊤) trivial
    have hsub : ∀ w : Sp Ω, w = ξ := fun w => Subsingleton.elim _ _
    have hpV : ⊤ ≤ p ⁻¹ᵁ V := fun w _ => by rw [hsub w]; exact hxV
    have hξB : ξ ∈ p ⁻¹ᵁ V := hxV
    letI := (p.app V).hom.toAlgebra

    let gB := (Sp Ω).presheaf.germ (p ⁻¹ᵁ V) ξ hξB
    let gR := Z.presheaf.germ V (p ξ) hxV
    have hsq : gR ≫ p.stalkMap ξ = p.app V ≫ gB := p.germ_stalkMap V ξ hxV
    letI alO : Algebra Γ(Z, V) (Z.presheaf.stalk (p ξ)) :=
      TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨p ξ, hxV⟩
    letI alS : Algebra (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) := (p.stalkMap ξ).hom.toAlgebra
    letI alRS : Algebra Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) := (gR ≫ p.stalkMap ξ).hom.toAlgebra
    haveI : IsScalarTower Γ(Z, V) (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI hloc : IsLocalization.AtPrime (Z.presheaf.stalk (p ξ)) (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal :=
      hV.isLocalization_stalk ⟨p ξ, hxV⟩

    have h1 : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (p ⁻¹ᵁ V) := hpV
    let E : Γ(Sp Ω, p ⁻¹ᵁ V) →+* Ω := (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
    have hE : ∀ b, E b = valR (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) b := fun b => (GlobalTheory.Points.valR_eq _ _ h1 b).symm
    have hEinj : Function.Injective E := by
      have e1 : GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1 =
          (Sp Ω).presheaf.map (homOfLE h1).op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
        rw [GlobalTheory.Points.valMap, Scheme.Hom.appLE]
        simp
        rfl
      haveI : Nonempty (⊤ : (Sp Ω).Opens) := ⟨⟨ξ, trivial⟩⟩
      show Function.Injective (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
      rw [e1]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1.comp
        (map_injective_of_isIntegral (Sp Ω) (homOfLE h1))
    obtain ⟨y', hy'⟩ : ∃ y' : Γ(Sp Ω, p ⁻¹ᵁ V), E y' = x := by
      refine ⟨((Sp Ω).presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x), ?_⟩
      rw [hE, GlobalTheory.Points.valR_res (𝟙 (Sp Ω)) le_top h1]
      have := GlobalTheory.Points.valR_specMap (𝟙 (CommRingCat.of Ω)) x
      rw [Spec.map_id] at this
      exact this

    let y := gB.hom y'
    have hy : IsIntegral (Z.presheaf.stalk (p ξ)) y := hfin.to_isIntegral y
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal.primeCompl y hy
    have hcomm : ∀ r : Γ(Z, V), gB.hom (algebraMap Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V) r) =
        algebraMap Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) r := fun r => by
      show gB.hom ((p.app V).hom r) = (gR ≫ p.stalkMap ξ).hom r
      rw [hsq]; rfl
    let gB' : Γ(Sp Ω, p ⁻¹ᵁ V) →ₐ[Γ(Z, V)] (Sp Ω).presheaf.stalk ξ := { gB.hom with commutes' := hcomm }
    have hgB : Function.Injective gB' := germ_injective_of_isIntegral (Sp Ω) ξ hξB
    let c' : Γ(Sp Ω, p ⁻¹ᵁ V) := algebraMap Γ(Z, V) _ (m : Γ(Z, V))
    let d' : Γ(Sp Ω, p ⁻¹ᵁ V) := c' * y'
    have hc : IsIntegral Γ(Z, V) c' := isIntegral_algebraMap
    have hd : IsIntegral Γ(Z, V) d' := by
      rw [← isIntegral_algHom_iff gB' hgB]
      have : gB' d' = (m : Γ(Z, V)) • y := by
        rw [Algebra.smul_def, map_mul]
        exact congrArg (· * y) (hcomm _)
      rw [this]
      exact hm
    have hc0 : c' ≠ 0 := by
      intro h0
      have h2 : IsUnit (gB.hom c') := by
        rw [hcomm]
        exact ((IsLocalization.map_units (Z.presheaf.stalk (p ξ)) m).map (p.stalkMap ξ).hom)
      rw [h0, map_zero] at h2
      exact not_isUnit_zero h2
    have hEc : E c' ≠ 0 := fun h0 => hc0 (hEinj (h0.trans (map_zero E).symm))

    let iso := p.normalizationObjIso hV
    have key := p.normalizationObjIso_hom_val hV
    let ac : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨c', hc⟩
    let ad : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨d', hd⟩
    have hle : p ⁻¹ᵁ V ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := by
      simp [← Scheme.Hom.comp_preimage]
    have hval : ∀ e : integralClosure Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V),
        valR p.toNormalization (p.fromNormalization ⁻¹ᵁ V) (iso.inv.hom e) = E e.1 := by
      intro e
      have h3 := congrArg (fun φ => φ.hom (iso.inv.hom e)) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at h3
      rw [hE, ← Category.id_comp p.toNormalization, ← GlobalTheory.Points.valR_appLE (𝟙 (Sp Ω)) p.toNormalization hle h1]
      congr 1
      exact h3.symm
    have hW : ⊤ ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := h1.trans hle
    have hU : ⊤ ≤ p.toNormalization ⁻¹ᵁ p.normalization.basicOpen ac := by
      rw [GlobalTheory.Points.le_preimage_basicOpen_iff _ hW ac]
      exact (show valR p.toNormalization _ ac ≠ 0 from (hval _).trans_ne hEc).isUnit
    have hu : IsUnit ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) :=
      p.normalization.toRingedSpace.isUnit_res_basicOpen ac
    refine ⟨p.normalization.basicOpen ac,
      (p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ad * ↑(hu.unit⁻¹),
      ⟨_, hU (x := ξ) trivial⟩, ?_⟩
    rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valR_mul _ _ hU, GlobalTheory.Points.valR_res _ _ hU, hval]
    have h4 : valR p.toNormalization _ ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) *
        valR p.toNormalization (p.normalization.basicOpen ac) ↑(hu.unit⁻¹) = 1 := by
      rw [← GlobalTheory.Points.valR_mul _ _ hU, ← GlobalTheory.Points.valR_one p.toNormalization _ hU]
      congr 1
      exact hu.mul_val_inv
    rw [GlobalTheory.Points.valR_res _ _ hU, hval] at h4
    rw [eq_inv_of_mul_eq_one_right h4]
    show E (c' * y') * (E c')⁻¹ = x
    rw [map_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hEc, one_mul, hy']
  haveI := IsSeparated.of_comp s (spMap κ)
  haveI := locallyOfFiniteType_of_comp s (spMap κ)
  haveI := QuasiCompact.of_comp s (spMap κ)
  let M : RatModel o Ω :=
    { Z := p.normalization
      s := s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := p.toNormalization
      pt_s := hpt_s
      gen := hgen
      onto := honto }
  exact ⟨M, p.fromNormalization, GlobalTheory.IsNormalScheme.pred _, inferInstance, p.toNormalization_fromNormalization⟩

end GlobalTheory.Poinc
