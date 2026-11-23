import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualOfDualSubgroups
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallDualLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousDistribHaarCharUnitsOfCompactOpen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHaarQuotientIntegralFormula

open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.EtMeas

theorem top_facts (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] :
    IsTopologicalAddGroup V ∧ T2Space V ∧ LocallyCompactSpace V ∧ SecondCountableTopology V ∧
      ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty := by
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup F V
  let b := Module.finBasis F V
  have : T2Space V := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  let e := b.equivFunL.toHomeomorph
  refine ⟨‹_›, ‹_›, e.isOpenEmbedding.locallyCompactSpace, e.secondCountableTopology,
    e ⁻¹' Metric.closedBall 0 1, ?_, ?_, ?_⟩
  · exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage e.continuous
  · exact e.isCompact_preimage.2 (isCompact_closedBall _ _)
  · exact ⟨e.symm 0, by simp⟩

theorem exists_selfDual (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V]
    [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V) (hs : β.IsSymm) (hn : β.Nondegenerate) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) := by
  obtain ⟨_, _, _, _, -⟩ := top_facts F V
  obtain ⟨hc, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  refine GlobalTheory.JR.exists_selfDual_of_dual_subgroups V (fun x y => ψ (β x y)) hc (fun x y => by rw [hs.eq]) (fun x x' y => ?_)
    (fun y => by simp) hl
  simp [AddChar.map_add_eq_mul]

theorem eq_zero_of_trace (F : Type) [Field F] [CharZero F] (K : Type) [CommRing K] [Algebra F K]
    [Module.Finite F K] [IsReduced K] (x : K) (hx : ∀ y, Algebra.trace F K (x * y) = 0) : x = 0 := by
  have : IsArtinianRing K := IsArtinianRing.of_finite F K
  have : IsSemisimpleRing K := IsArtinianRing.isSemisimpleRing_of_isReduced K
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})
  have h1 : e ∈ Ideal.span {x} := hI ▸ Ideal.mem_span_singleton_self e
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : IsIdempotentElem (Algebra.lmul F K e) := he.map _
  have h3 : LinearMap.trace F K (Algebra.lmul F K e) = 0 := by
    have := hx y
    rwa [mul_comm, hy, Algebra.trace_apply] at this
  have h4 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff h2).1 h3
  have h5 : e = 0 := by simpa using LinearMap.congr_fun h4 1
  have h6 : x ∈ Ideal.span {e} := hI ▸ Ideal.mem_span_singleton_self x
  simpa [h5] using h6

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem star_smul_K (A : Et F E) (k : A.K) (y : A.L) : star (k • y) = k • star y := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul', A.star_K]

theorem star_smul_F (A : Et F E) (c : F) (y : A.L) : star (c • y) = c • star y := by
  rw [← algebraMap_smul A.K c y, star_smul_K, algebraMap_smul]

def starF (A : Et F E) : A.L →ₗ[F] A.L where
  toFun := star
  map_add' := star_add
  map_smul' := star_smul_F A

theorem finite_L [Unram F E] (A : Et F E) : Module.Finite F A.L := by
  obtain ⟨⟨b⟩, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : Module.Finite A.K A.L := Module.Finite.of_basis b
  exact Module.Finite.trans A.K A.L

theorem exists_selfDual_K [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    ∃ μ : Measure A.K, SelfDual μ (A.kerK ψ) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have hs : (Algebra.traceForm F A.K).IsSymm := ⟨fun x y => by simp [mul_comm]⟩
  refine exists_selfDual F ψ hψ A.K (Algebra.traceForm F A.K) hs ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact eq_zero_of_trace F A.K x fun y => by simpa using hx y
  · exact eq_zero_of_trace F A.K x fun y => by simpa [mul_comm] using hx y

def formL (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.L :=
  ((LinearMap.mul F A.L).comp (starF A)).compr₂
    ((Algebra.trace F A.K).comp ((LinearMap.mul F A.K x).comp ((Algebra.trace A.K A.L).restrictScalars F)))

theorem formL_apply (A : Et F E) (x : A.K) (y' y : A.L) :
    formL A x y' y = Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)) := rfl

theorem exists_selfDual_L [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.Kˣ) :
    ∃ μ : Measure A.L, SelfDual μ (A.kerL ψ x) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := finite_L A
  obtain ⟨-, hinj, -, htr, hnd⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hs : (formL A x).IsSymm := ⟨fun y y' => by
    rw [formL_apply, formL_apply]
    congr 2
    apply hinj
    rw [htr, htr]; simp [add_comm, mul_comm]⟩
  have hl : ∀ y', (∀ y, formL A x y' y = 0) → y' = 0 := fun y' h => hnd y' fun y => by
    have h1 : (x : A.K) * Algebra.trace A.K A.L (star y' * y) = 0 := eq_zero_of_trace F A.K _ fun k => by
      have := h (k • y)
      rw [formL_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    simpa using h1
  exact exists_selfDual F ψ hψ A.L (formL A x) hs ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩

theorem exists_isReps (A : Et F E) : ∃ S : Set A.Kˣ, A.IsReps S := by
  let H : Subgroup A.Kˣ := (Units.map (Algebra.norm A.K : A.L →* A.K)).range
  have key : ∀ a x : A.Kˣ, (∃ y : A.L, IsUnit y ∧ (a : A.K) = x * A.NL y) ↔
      (QuotientGroup.mk x : A.Kˣ ⧸ H) = QuotientGroup.mk a := by
    intro a x
    rw [QuotientGroup.eq]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨hy.unit, Units.ext ?_⟩
      simp [h, Et.NL]
    · rintro ⟨y, h⟩
      refine ⟨y, y.isUnit, ?_⟩
      have := congrArg Units.val h
      simp only [Units.coe_map, Units.val_mul] at this
      rw [Et.NL, this]; simp
  refine ⟨Set.range (Quotient.out : A.Kˣ ⧸ H → A.Kˣ), fun a => ⟨Quotient.out (QuotientGroup.mk a : A.Kˣ ⧸ H),
    ⟨⟨_, rfl⟩, (key _ _).2 (QuotientGroup.out_eq' _)⟩, ?_⟩⟩
  rintro _ ⟨⟨q, rfl⟩, h⟩
  rw [← (key _ _).1 h, QuotientGroup.out_eq']

theorem borel_units (R : Type) [CommRing R] [TopologicalSpace R] [IsOpenUnits R] [MeasurableSpace R] [BorelSpace R] :
    BorelSpace Rˣ := by
  have h := (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isInducing
  refine ⟨?_⟩
  have h1 := @borel_comap Rˣ R Units.val inferInstance
  rw [← BorelSpace.measurable_eq (α := R), ← h.eq_induced] at h1
  exact h1.symm

theorem absK_unit (A : Et F E) (u : A.Kˣ) : A.absK u = distribHaarChar A.K u := by
  simp [Et.absK]

theorem continuous_NL [U : Unram F E] (A : Et F E) : Continuous A.NL := by
  have := finite_L A
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (IsScalarTower.toAlgHom F A.K A.L).toLinearMap
    (LinearMap.ker_eq_bot.2 hinj)
  have h1 : A.NL = fun y => r (y * starF A y) := by
    funext y
    have := LinearMap.congr_fun hr (A.NL y)
    rw [← show _ = A.NL y from this]
    exact congrArg r (hN y)
  rw [h1]
  exact (IsModuleTopology.continuous_of_linearMap r).comp
    (continuous_id.mul (IsModuleTopology.continuous_of_linearMap (starF A)))

def normU (A : Et F E) : A.Lˣ →* A.Kˣ := Units.map (Algebra.norm A.K : A.L →* A.K)

theorem normU_val (A : Et F E) (y : A.Lˣ) : (normU A y : A.K) = A.NL y := rfl

theorem isOpen_range [U : Unram F E] (A : Et F E) : IsOpen ((normU A).range : Set A.Kˣ) := by
  have := U.charZero; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨-, hsq⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.K
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h1 : ∀ᶠ v : A.Kˣ in 𝓝 1, ∃ s : A.K, s ^ 2 = v := (Units.continuous_val.tendsto 1).eventually hsq
  filter_upwards [h1] with v ⟨s, hs⟩
  have hu : IsUnit s := (isUnit_pow_iff two_ne_zero).1 (hs ▸ v.isUnit)
  refine ⟨(hu.map (algebraMap A.K A.L)).unit, Units.ext (hinj ?_)⟩
  rw [normU_val, hN, IsUnit.unit_spec, A.star_K, ← map_mul, ← hs, sq]

theorem isSES [U : Unram F E] (A : Et F E) :
    TopologicalGroup.IsSES (Unitary.toUnits : unitary A.L →* A.Lˣ) (normU A).rangeRestrict := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := finite_L A
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, -, _, -⟩ := top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨_, -⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.K
  obtain ⟨_, -⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.L
  have hK := IsOpenUnits.isOpenEmbedding_unitsVal (M := A.K)
  have hL := IsOpenUnits.isOpenEmbedding_unitsVal (M := A.L)
  have hc : Continuous (normU A) := Units.continuous_map (continuous_NL A)
  have hker : ∀ y : A.Lˣ, normU A y = 1 ↔ y ∈ Set.range (Unitary.toUnits : unitary A.L →* A.Lˣ) := by
    intro y
    constructor
    · intro h
      have h1 : (y : A.L) * star (y : A.L) = 1 := by rw [← hN, ← normU_val, h]; simp
      exact ⟨⟨y, by rw [mul_comm]; exact h1, h1⟩, Units.ext rfl⟩
    · rintro ⟨t, rfl⟩
      refine Units.ext (hinj ?_)
      rw [normU_val, hN]
      simp
  have : LocallyCompactSpace A.Lˣ := hL.locallyCompactSpace
  have : LocallyCompactSpace A.Kˣ := hK.locallyCompactSpace
  have : SecondCountableTopology A.Lˣ := hL.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace (normU A).range := (isOpen_range A).locallyCompactSpace
  have hc' : Continuous (normU A).rangeRestrict := hc.subtype_mk _
  refine ⟨⟨?_, ?_⟩, ⟨(normU A).rangeRestrict_surjective, hc',
    MonoidHom.isOpenMap_of_sigmaCompact _ (normU A).rangeRestrict_surjective hc'⟩, fun y => ?_⟩
  · exact hL.isEmbedding.of_comp_iff.1 IsEmbedding.subtypeVal
  · rw [show Set.range (Unitary.toUnits : unitary A.L →* A.Lˣ) = normU A ⁻¹' {1} from
      Set.ext fun y => (hker y).symm]
    exact isClosed_singleton.preimage hc
  · rw [← hker y, Subtype.ext_iff]; rfl

theorem exists_isNat [U : Unram F E] (A : Et F E) (μK : Measure A.K) (μL : Measure A.L)
    (hμK : μK.IsAddHaarMeasure) (hμL : μL.IsAddHaarMeasure) : ∃ ν, A.IsNat μK μL ν := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := finite_L A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, -, _, hSK⟩ := top_facts F A.K
  obtain ⟨_, _, _, _, hSL⟩ := top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (starF A)⟩
  obtain ⟨_, -⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.K
  obtain ⟨_, -⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.L
  have hK := IsOpenUnits.isOpenEmbedding_unitsVal (M := A.K)
  have hL := IsOpenUnits.isOpenEmbedding_unitsVal (M := A.L)
  have : LocallyCompactSpace A.Lˣ := hL.locallyCompactSpace
  have : SecondCountableTopology A.Lˣ := hL.isEmbedding.secondCountableTopology
  have := borel_units A.K
  have := borel_units A.L
  have : SecondCountableTopology A.Kˣ := hK.isEmbedding.secondCountableTopology
  have hδ : ∀ y : A.Lˣ, ((A.absK (A.NL y) : ℝ) : ℂ) = ((distribHaarChar A.L y : ℝ) : ℂ) := by
    intro y
    rw [← normU_val, absK_unit]
    have := GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) y (normU A y) (hN y)
    rw [this]
  obtain ⟨mK, hmK, hfK⟩ := GlobalTheory.exists_isHaarMeasure_units_div_module A.K μK hμK hSK
  obtain ⟨mL, hmL, hfL⟩ := GlobalTheory.exists_isHaarMeasure_units_div_module A.L μL hμL hSL
  have hop := isOpen_range A
  have hC : (mK.comap (normU A).range.subtype).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) mK hop.isOpenEmbedding_subtypeVal
  obtain ⟨ν, hν, hf⟩ := GlobalTheory.JR.exists_haar_quotient_integral_formula _ _ _ _ _ (isSES A) mL _ hmL hC
  refine ⟨ν, hν, fun s hs h hh hsupp => ?_⟩
  have hs' : ∀ c : (normU A).range, A.NL (s (c : A.Kˣ)) = (c : A.Kˣ) := by
    rintro ⟨_, y, rfl⟩
    exact hs y y.isUnit
  have hu : ∀ c : (normU A).range, IsUnit (s (c : A.Kˣ)) := fun c => by
    have h1 := (c : A.Kˣ).isUnit.map (algebraMap A.K A.L)
    rw [← hs' c, hN] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hcs : HasCompactSupport fun u : A.Lˣ => h u := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Units.val ⁻¹' tsupport h) ?_
      fun u hu => subset_tsupport h hu
    refine hL.isInducing.isCompact_preimage' hh.2 fun y hy => ?_
    exact hsupp hy
  have e1 := hf (fun u => h u) (hh.1.continuous.comp Units.continuous_val) hcs (fun c => (hu c).unit)
    (fun c => Subtype.ext (Units.ext (hs' c)))
  have e2 := hfL h (fun y => ((A.absK (A.NL y) : ℝ) : ℂ)) hδ Set.univ MeasurableSet.univ
  have e3 := hfK (fun a => A.orbL ν h (s a)) (fun a => ((A.absK a : ℝ) : ℂ)) (fun u => by rw [absK_unit])
    _ hop.measurableSet
  have hset : {a : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a} = Units.val '' ((normU A).range : Set A.Kˣ) := by
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨hy.unit, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, y.isUnit, rfl⟩
  rw [hset, ← e3, ← integral_subtype_comap hop.measurableSet,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Units.val '' (Set.univ : Set A.Lˣ)), ← e2,
    Measure.restrict_univ, e1]
  · refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    simp only [Et.orbL]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    exact congrArg h (mul_comm _ _)
  · intro y hy
    have : h y = 0 := image_eq_zero_of_notMem_tsupport fun h1 => by
      obtain ⟨u, hu⟩ := hsupp h1
      exact hy ⟨u, trivial, hu⟩
    simp [this]

theorem nonempty_meas_and_reps : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (A : GlobalTheory.JR.Et F E) (ψ : AddChar F ℂ),
    GlobalTheory.JR.IsStdChar ψ → Nonempty (A.Meas ψ) ∧ ∃ S : Set A.Kˣ, A.IsReps S := by
  intro F E _ _ _ _ _ A ψ hψ
  obtain ⟨μK, hK⟩ := exists_selfDual_K A ψ hψ
  choose μL hL using exists_selfDual_L A ψ hψ
  obtain ⟨ν, hν⟩ := exists_isNat A μK (μL 1) hK.1 (hL 1).1
  exact ⟨⟨⟨μK, μL, ν, hK, hL, hν⟩⟩, exists_isReps A⟩

end GlobalTheory.JR.EtMeas
