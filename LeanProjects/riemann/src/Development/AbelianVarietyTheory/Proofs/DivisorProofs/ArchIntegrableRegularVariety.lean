import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableOnOfNormLeSumAbsLogAddLogLog

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory.LogNormInt

theorem integrableOn_of_chart {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}
    (e : OpenPartialHomeomorph M (V n)) {μ : Measure M} {ρ : V n → ℝ≥0∞}
    (hμ : ∀ A, MeasurableSet A → A ⊆ e.source → μ A = ∫⁻ v in e '' A, ρ v)
    {A : Set M} (hA : MeasurableSet A) (hAs : A ⊆ e.source) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hρ : ∀ v ∈ e '' A, ρ v ≤ C) {f : M → ℝ} (hf : ContinuousOn f A)
    (hi : IntegrableOn (f ∘ e.symm) (e '' A)) : IntegrableOn f A μ := by
  have hm := measurableSet_image e hA hAs
  have hsub : e '' A ⊆ e.target := fun _ ⟨y, hy, h⟩ => h ▸ e.map_source (hAs hy)
  have hs : AEMeasurable e.symm (volume.restrict (e '' A)) :=
    (e.continuousOn_symm.mono hsub).aemeasurable hm
  have hle : μ.restrict A ≤ C • Measure.map e.symm (volume.restrict (e '' A)) := by
    refine Measure.le_iff.2 fun B hB => ?_
    have hBA := hB.inter hA
    have hm' := measurableSet_image e hBA (inter_subset_right.trans hAs)
    rw [Measure.restrict_apply hB, hμ _ hBA (inter_subset_right.trans hAs), Measure.smul_apply,
      Measure.map_apply_of_aemeasurable hs hB, Measure.restrict_apply' hm, smul_eq_mul]
    refine (setLIntegral_mono' hm' fun v hv => hρ v (image_mono inter_subset_right hv)).trans ?_
    rw [setLIntegral_const]
    gcongr
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨by rw [mem_preimage, e.left_inv (hAs hy.2)]; exact hy.1, mem_image_of_mem _ hy.2⟩
  refine ⟨hf.aestronglyMeasurable hA, ?_⟩
  refine (lintegral_mono' hle le_rfl).trans_lt ?_
  rw [lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.mul_lt_top hC.lt_top ((lintegral_map_le _ _).trans_lt hi.2)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem continuousAt_ratVal {f : X.functionField} {y : CxPts p σ} (hf : RegAt (under y) f) :
    ContinuousAt (fun z : CxPts p σ => ratVal f z) y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hn := (isOpen_ptsIn (p := p) (σ := σ) U).mem_nhds (mem_ptsIn.2 hU)
  refine ((continuousOn_ev a).continuousAt hn).congr ?_
  filter_upwards [hn] with z hz
  exact (ratVal_fnOf hz _ a).symm

theorem frequently_ne_zero (hσ : Function.Injective σ) (c : AlgChart p σ D) {U : X.Opens}
    {a : Γ(X, U)} (ha : a ≠ 0) {y : CxPts p σ} (hy : y ∈ c.e.source) (hU : y ∈ ptsIn p σ U) :
    ∃ᶠ v in 𝓝 (c.e y), (ev p σ U a ∘ c.e.symm) v ≠ 0 := by
  have : IsDomain k := hσ.isDomain σ
  have hg := gen_mem (mem_ptsIn.1 hU)
  have hb : genericPoint X ∈ X.basicOpen a := (unitAt_fnOf_iff hg hg a).1
    (unitAt_genericPoint ((map_ne_zero_iff _ (fnOf_injective U hg)).2 ha))
  have h := Measure.dense_of_ae (SemiPosBir.ae_mem hσ c (U := X.basicOpen a) ⟨_, hb⟩)
  have h₁ := mem_closure_iff_frequently.1 (h (c.e y))
  refine (h₁.and_eventually ((isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (mem_over c.e hy hU))).mono ?_
  rintro v ⟨h₂, h₃⟩
  exact (mem_ptsIn_basicOpen h₃.2 a).1 (h₂ h₃.1)

theorem exists_integrableOn [SecondCountableTopology (CxPts p σ)] (hσ : Function.Injective σ)
    {A B : LB X} {ψ : Weight p σ A} (hψ : ψ.IsCInf) {φ : Weight p σ B} (hφ : φ.IsCInf)
    {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) (ε : ℤˣ) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm φ r)
      (offSupp p σ (divOfRatSec φ.isLB hr) ∩ O) (ψ.chernPart D ε) := by
  set i := pick φ.isLB y
  have hi : y ∈ ptsIn p σ (B.U i) := mem_pick _ y
  have hyU := c.source_subset hy
  have hg := gen_mem (mem_ptsIn.1 hyU)
  have : Nonempty c.U := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X c.U c.affine
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, c.U)) (r i : X.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  change fnOf c.U hg a / fnOf c.U hg b = _ at hab
  have hb1 : fnOf c.U hg b ≠ 0 := (map_ne_zero_iff _ (fnOf_injective _ hg)).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact (r i).ne_zero hab.symm
  have hT := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) c.U)).mem_nhds (mem_over c.e hy hyU)
  have hd (s : Γ(X, c.U)) : ∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ (ev p σ c.U s ∘ c.e.symm) v :=
    (c.holo _ s).eventually_differentiableAt hT
  obtain ⟨δ, hδ, hae, hint⟩ := exists_integrableOn_log_norm_div volume (hd a) (hd b)
    (frequently_ne_zero hσ c ha0 hy hyU) (frequently_ne_zero hσ c hb0 hy hyU)
  have hT' := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))).mem_nhds (mem_over c.e hy hi)
  obtain ⟨η, hη, hηs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hT' (ball_mem_nhds _ hδ))
  have hcont : ContinuousOn (fun v => c.chernDens ψ (c.e.symm v)) c.e.target :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      ((Continuous.matrix_det continuous_id).comp_continuousOn
        ((GlobalTheory.MixDens.chernMat_isForm k X p σ D _ ψ hψ).2.1 c)))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (c.e y) η).exists_bound_of_continuousOn
    (hcont.mono fun v hv => (hηs hv).1.1)
  set O := c.e.source ∩ c.e ⁻¹' ball (c.e y) η
  have hO : IsOpen O := c.e.continuousOn.isOpen_inter_preimage c.e.open_source isOpen_ball
  set S := offSupp p σ (divOfRatSec φ.isLB hr) ∩ O
  have hS : IsOpen S := (isOpen_offSupp _).inter hO
  have hSs : S ⊆ c.e.source := fun z hz => hz.2.1
  have him : c.e '' S ⊆ closedBall (c.e y) η := by
    rintro _ ⟨z, hz, rfl⟩
    exact ball_subset_closedBall hz.2.2
  have hSi (z) (hz : z ∈ S) : z ∈ ptsIn p σ (B.U i) := by
    have := (hηs (him (mem_image_of_mem _ hz))).1.2
    rwa [mem_preimage, c.e.left_inv (hSs hz)] at this
  have hm := measurableSet_image c.e hS.measurableSet hSs
  refine ⟨O, hO.mem_nhds ⟨hy, mem_ball_self hη⟩, integrableOn_of_chart c.e
    (fun A hA hAs => Weight.chernPart_apply hψ ε c hA hAs) hS.measurableSet hSs
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun v hv => ENNReal.ofReal_le_ofReal ?_) ?_ ?_⟩
  · have h := hC v (him hv)
    rw [Real.norm_eq_abs, abs_le] at h
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using h.2
    · simpa [neg_le] using h.1
  · refine ContinuousOn.congr (f := fun z => Real.log ‖ratVal (r i : X.functionField) z‖ - φ.φ i z / 2)
      (fun z hz => ContinuousAt.continuousWithinAt ?_) fun z hz => logNorm_eq φ hr hz.1 (hSi z hz)
    have hu := hr.unitAt φ.isLB hz.1 (hSi z hz)
    exact ((continuousAt_ratVal hu.regAt).norm.log (norm_ne_zero_iff.2 (ratVal_ne_zero hu))).sub
      ((hφ i z (hSi z hz)).continuousAt.div_const 2)
  · have hsub : c.e '' S ⊆ ball (c.e y) δ := fun v hv => (hηs (him hv)).2
    have h₁ : IntegrableOn (fun v => (φ.φ i ∘ c.e.symm) v / 2) (c.e '' S) :=
      (((((contDiffOn_chart (hφ i) c).continuousOn.mono fun v hv => (hηs hv).1).div_const
        2).integrableOn_compact (isCompact_closedBall _ _)).mono_set him)
    refine ((hint.mono_set hsub).sub h₁).congr ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hae, ae_restrict_mem hm] with v hv hv'
    obtain ⟨z, hz, rfl⟩ := hv'
    have hzU := c.source_subset (hSs hz)
    have hu := hr.unitAt φ.isLB hz.1 (hSi z hz)
    have e := ratVal_mul hu.regAt (regAt_fnOf (mem_ptsIn.1 hzU) hg b)
    rw [← hab, div_mul_cancel₀ _ hb1, hab, ratVal_fnOf hzU, ratVal_fnOf hzU] at e
    simp only [Function.comp_apply, Pi.sub_apply, c.e.left_inv (hSs hz)] at hv ⊢
    rw [logNorm_eq φ hr hz.1 (hSi z hz), e, mul_div_cancel_right₀ _ hv.2]

theorem archIntegrable : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ}, GlobalTheory.CxForm.IsRegVar p D → ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ} (hr : IsRatSec N.B r),
      M.ArchIntegrable N D hr := by
  intro k _ X _ p D hX M N r hr σ
  have := hX.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := RegGenSmooth.genSmooth hX.toIsArithVar hX.regular σ
  have hσ : Function.Injective σ := ChernNull.injective_of_arithVar hX.toIsArithVar σ
  have key (ε : ℤˣ) : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr))
      ((M.φ σ).chernPart D ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm (N.φ σ) r)
        (offSupp p σ (N.div hr) ∩ O) ((M.φ σ).chernPart D ε) :=
      have ⟨_, hi⟩ := R.cover y
      exists_integrableOn hσ (M.cInf σ) (N.cInf σ) hr ε _ hi
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
    obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.LogNormInt
