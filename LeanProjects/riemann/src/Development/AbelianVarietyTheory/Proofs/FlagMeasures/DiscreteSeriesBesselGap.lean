import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselQuotientMassEqConstMulNormSqTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFinNeZeroOfCwCont
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNonneg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapCondition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecSmoothAtGapOfDecSmooth
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselPeriodNonzero

open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.BesselPeriodNonzero.sq_int {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    {ν : Measure X} {f : X → E} {a : ℝ}
    (hf : AEStronglyMeasurable f ν) (ha : 0 ≤ a) (h : ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂ν = ENNReal.ofReal a) :
    Integrable (fun x => ‖f x‖ ^ 2) ν ∧ ∫ x, ‖f x‖ ^ 2 ∂ν = a := by
  have key : ∀ x, ENNReal.ofReal (‖f x‖ ^ 2) = (‖f x‖₊ : ℝ≥0∞) ^ 2 := by
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]
  have hm : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) ν := hf.norm.pow 2
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)]
    simp_rw [key, h]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hm]
    simp_rw [key, h]
    exact ENNReal.toReal_ofReal ha

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.BesselPeriodNonzero.inner_int {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ν : Measure X}
    {f g : X → E} (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (h1 : Integrable (fun x => ‖f x‖ ^ 2) ν) (h2 : Integrable (fun x => ‖g x‖ ^ 2) ν) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) ν ∧
      ∫ x, ‖⟪f x, g x⟫_ℂ‖ ∂ν ≤ ∫ x, ‖f x‖ ^ 2 ∂ν + ∫ x, ‖g x‖ ^ 2 ∂ν ∧
      2 * (∫ x, ⟪f x, g x⟫_ℂ ∂ν).re = ∫ x, ‖f x + g x‖ ^ 2 ∂ν - ∫ x, ‖f x‖ ^ 2 ∂ν - ∫ x, ‖g x‖ ^ 2 ∂ν := by
  have hb : ∀ x, ‖⟪f x, g x⟫_ℂ‖ ≤ ‖f x‖ ^ 2 + ‖g x‖ ^ 2 := by
    intro x
    have := norm_inner_le_norm (𝕜 := ℂ) (f x) (g x)
    nlinarith [sq_nonneg (‖f x‖ - ‖g x‖), norm_nonneg (f x), norm_nonneg (g x)]
  have hint : Integrable (fun x => ⟪f x, g x⟫_ℂ) ν :=
    Integrable.mono' (h1.add h2) (hf.inner hg) (ae_of_all _ hb)
  refine ⟨hint, ?_, ?_⟩
  · rw [← integral_add h1 h2]
    exact integral_mono hint.norm (h1.add h2) hb
  · have e : (fun x => ‖f x + g x‖ ^ 2) = fun x => ‖f x‖ ^ 2 + 2 * (⟪f x, g x⟫_ℂ).re + ‖g x‖ ^ 2 :=
      funext fun x => norm_add_sq (𝕜 := ℂ) (f x) (g x)
    have hre : Integrable (fun x => 2 * (⟪f x, g x⟫_ℂ).re) ν := hint.re.const_mul 2
    have hre' : ∫ x, (⟪f x, g x⟫_ℂ).re ∂ν = (∫ x, ⟪f x, g x⟫_ℂ ∂ν).re := integral_re hint
    have s1 : ∫ x, (‖f x‖ ^ 2 + 2 * (⟪f x, g x⟫_ℂ).re + ‖g x‖ ^ 2) ∂ν =
        ∫ x, (‖f x‖ ^ 2 + 2 * (⟪f x, g x⟫_ℂ).re) ∂ν + ∫ x, ‖g x‖ ^ 2 ∂ν := integral_add (h1.add hre) h2
    have s2 : ∫ x, (‖f x‖ ^ 2 + 2 * (⟪f x, g x⟫_ℂ).re) ∂ν =
        ∫ x, ‖f x‖ ^ 2 ∂ν + ∫ x, 2 * (⟪f x, g x⟫_ℂ).re ∂ν := integral_add h1 hre
    rw [e, s1, s2, integral_const_mul, hre']
    ring

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.BesselPeriodNonzero.unfold_zero {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : _root_.BranchingSupport.Rep k r}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)} {B : R.H → Wp} {w v : R.H} (hK : _root_.PI.KFinSmooth) (hR : R.IsDS ε mu)
    (hS : _root_.BranchingSupport.SideG k r z π u μW μN μG νq) (hB : _root_.BranchingSupport.IsBes R z π B) (hw : w ∈ R.sm)
    (hbe : ∀ x ∈ R.sm, Integrable (_root_.Formalism.FourierDecayAlt.ThreeDimData.beInt z _root_.Formalism.QuantumDeterminants.cStd π R.σ x v) (μW.prod μN) ∧
      _root_.Formalism.FourierDecayAlt.ThreeDimData.be z _root_.Formalism.QuantumDeterminants.cStd π R.σ μW μN x v = 0) (ξ : Wp)
    (hi : Integrable (fun g : _root_.Formalism.QuantumDeterminants.Mt k r => star ⟪v, R.σ (Matrix.of g) w⟫_ℂ * ⟪ξ, B (R.σ (Matrix.of g) w)⟫_ℂ) μG) :
    ∫ g : _root_.Formalism.QuantumDeterminants.Mt k r, star ⟪v, R.σ (Matrix.of g) w⟫_ℂ * ⟪ξ, B (R.σ (Matrix.of g) w)⟫_ℂ ∂μG = 0 := by
  obtain ⟨hz, hzpos, ⟨u₀, hπ⟩, -, hW, hN, hG, hQ⟩ := hS
  have hB' := hB
  unfold _root_.BranchingSupport.IsBes _root_.PI.BesselMapUniq.IsBesselMapSm at hB'
  obtain ⟨-, -, hEq, -⟩ := hB'
  obtain ⟨hσmul, -, -, hσsm, -⟩ := _root_.GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  obtain ⟨-, hPU, hE, -⟩ := _root_.GlobalTheory.muSof_isHaar k r z μW μN hz hzpos hW hN
  unfold _root_.PI.IsHaarOnM at hE
  unfold _root_.PI.BesselPeriodGGP.IsHaarOn at hW hN hG
  haveI : SigmaFinite μW := hW.1
  haveI : SigmaFinite μN := hN.1
  haveI : SFinite (_root_.Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) := by unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.muSof; infer_instance
  set F : _root_.Formalism.QuantumDeterminants.Mt k r → ℂ := fun g => star ⟪v, R.σ (Matrix.of g) w⟫_ℂ * ⟪ξ, B (R.σ (Matrix.of g) w)⟫_ℂ with hFdef
  set G := hi.1.mk F
  have hGm : Measurable G := hi.1.stronglyMeasurable_mk.measurable
  have hFG : F =ᵐ[μG] G := hi.1.ae_eq_mk
  rw [integral_congr_ae hFG]
  refine _root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.quot_zero hQ G hGm (hi.congr hFG) ?_
  set T := toMeasurable μG {g | F g ≠ G g}
  have hT0 : μG T = 0 := by rw [measure_toMeasurable]; exact ae_iff.mp hFG
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hmul : ∀ x : _root_.Formalism.QuantumDeterminants.Mt k r, Measurable fun s : _root_.Formalism.QuantumDeterminants.Mt k r => _root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.mulMt s x := fun x =>
    (_root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.measurable_mulMt (k := k) (r := r)).comp (measurable_id.prodMk measurable_const)
  have hnull : ∀ᵐ x ∂νq, ∀ᵐ s ∂(_root_.Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN), _root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.mulMt s x ∉ T := by
    have h0 := hQ (T.indicator 1) (measurable_one.indicator hTm)
    have hmeas : Measurable fun x : _root_.Formalism.QuantumDeterminants.Mt k r =>
        ∫⁻ s, T.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(_root_.Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) :=
      ((measurable_one.indicator hTm).comp (_root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.measurable_mulMt (k := k) (r := r))).lintegral_prod_left'
    rw [lintegral_indicator_one hTm, hT0, eq_comm, lintegral_eq_zero_iff hmeas] at h0
    filter_upwards [h0] with x hx
    have hx' : ∫⁻ s, T.indicator 1 (_root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.mulMt s x) ∂(_root_.Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) = 0 := hx
    rw [lintegral_eq_zero_iff (f := fun s => T.indicator 1 (_root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.mulMt s x)) ((measurable_one.indicator hTm).comp (hmul x))] at hx'
    filter_upwards [hx'] with s hs hsT
    simp [Set.indicator_of_mem hsT] at hs
  have hxU : ∀ᵐ x ∂νq, Matrix.of x ∈ _root_.BranchingSupport.GG k r :=
    _root_.GlobalTheory.BesselNorm.quot_ae hQ (ae_iff.mpr hG.2.2.1)
      ((ae_iff.mpr hE.2.2.1).mono fun x hx => hPU hx) hE.2.1
  have hpW : ∀ᵐ p ∂μW.prod μN, Matrix.of p.1 ∈ _root_.Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ _root_.Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hW.2.2.1)).and
      (Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hN.2.2.1))
  have hm : Measurable (fun p : _root_.Formalism.QuantumDeterminants.Mt k r × _root_.Formalism.QuantumDeterminants.Mt k r => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) := by
    have hpair := _root_.GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap.measurable_mulP (k := k) (r := r)
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap.mulP at hpair
    exact hpair
  filter_upwards [hnull, hxU] with x hx hxU'
  have hy : R.σ (Matrix.of x) w ∈ R.sm := hσsm _ hxU' w hw
  obtain ⟨hint, hbe0⟩ := hbe _ hy
  unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.muSof at hx ⊢
  rw [integral_map (f := fun s => G (_root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.mulMt s x)) hm.aemeasurable (hGm.comp (hmul x)).aestronglyMeasurable]
  have hae : ∀ᵐ p ∂μW.prod μN, G (_root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
      (starRingEnd ℂ) ⟪B (R.σ (Matrix.of x) w), _root_.Formalism.FourierDecayAlt.ThreeDimData.beInt z _root_.Formalism.QuantumDeterminants.cStd π R.σ (R.σ (Matrix.of x) w) v p ξ⟫_ℂ := by
    filter_upwards [ae_of_ae_map hm.aemeasurable hx, hpW] with p hpT hp
    have hFG' : F (_root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
        G (_root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) := by
      by_contra hne
      exact hpT (subset_toMeasurable _ _ hne)
    rw [← hFG']
    have hprod : Matrix.of p.1 * Matrix.of p.2 ∈ _root_.BranchingSupport.GG k r := hPU ⟨_, hp.1, _, hp.2, rfl⟩
    have e1 : R.σ (Matrix.of (_root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x)) w =
        R.σ (Matrix.of p.1 * Matrix.of p.2) (R.σ (Matrix.of x) w) := by
      rw [← hσmul _ hprod _ hxU' w]; rfl
    have e2 := hEq _ hp.1 _ hp.2 _ hy
    simp only [F, e1, e2]
    unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.beInt
    rw [inner_smul_right, _root_.Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_inner hzpos hπ hp.1]
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, inner_smul_left, map_mul, Complex.star_def,
      inner_conj_symm, RCLike.conj_to_real, Complex.conj_conj]
    ring
  have hL := ((innerSL ℂ (B (R.σ (Matrix.of x) w))).comp
    (ContinuousLinearMap.apply ℂ Wp ξ)).integral_comp_comm hint
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply] at hL
  unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.be at hbe0
  rw [integral_congr_ae hae, integral_conj, hL, hbe0]
  simp

set_option maxHeartbeats 1600000 in

theorem nzOn_of_mass (hy : Hyps) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {R : Rep k r}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Mt k r)} {B l : R.H → Wp} {w : R.H} (hR : R.IsDS ε mu)
    (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hS : SideG k r z π u μW μN μG νq) (hB : IsBes R z π B) (hwK : R.KFin w) {c : ℝ} (hc : 0 ≤ c)
    (hiso : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = ENNReal.ofReal (c * ‖v‖ ^ 2))
    (h0 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0) (hl : IsBeL R z π μW μN l) :
    ∃ v ∈ R.sm, l v ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hK : PI.KFinSmooth := hy.1.2.2.1
  obtain ⟨hmul, hone, hun, hsm, hTK, hTKs, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have hwT := hKT w hwK
  have hw := hTK w hwT
  have hΦ := fun v hv => (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r ε mu R hR Wp B hB.1 hB.2.1 hB.2.2.2 v hv).1
  have hS' := hS
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hWh, hNh, hGh, hq⟩ := hS'
  have := hWh.1; have := hNh.1; have := hGh.1
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_id
  have hSeq : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN = (μW.prod μN).map (fun p => mulMt p.1 p.2) := rfl
  have hsf : SFinite (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) := by rw [hSeq]; infer_instance
  have hGm : MeasurableSet {y : Mt k r | Matrix.of y ∈ GG k r} := (isClosed_UH.preimage hof).measurableSet
  have hSae : ∀ᵐ s ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN), Matrix.of s ∈ GG k r := by
    rw [hSeq]
    refine (ae_map_iff measurable_mulMt.aemeasurable hGm).2 ?_
    filter_upwards [hPae] with p hp
    exact Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hS0 : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN ≠ 0 := GlobalTheory.SideCompare.muS_ne_zero hWh.2.1 hNh.2.1
  have hνae := GlobalTheory.BesselNorm.quot_ae hq hGae hSae hS0
  have hνs : SigmaFinite νq := GlobalTheory.SideCompare.sigmaFinite_of_isQuotMeas hS0 hq
  have hSC : SecondCountableTopology Wp := by
    have := FiniteDimensional.proper ℂ Wp
    infer_instance
  have one_mem : (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) ∈ GG k r := by
    show (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)ᴴ * Hpk k r * 1 = Hpk k r; simp
  have memDD : ∀ g ∈ GG k r, R.σ g w ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have wDD : w ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w := by
    have := memDD 1 one_mem; rwa [hone] at this
  have DDsm : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, v ∈ R.sm := by
    intro v hv
    refine hTK v (Submodule.span_le.2 ?_ hv)
    rintro _ ⟨g, hg, rfl⟩
    exact hTKs g hg w hwT
  have hnorm : ∀ g ∈ GG k r, ‖R.σ g w‖ = ‖w‖ := fun g hg => (sigma_facts hR.2).2 g hg w
  have hcw : c * ‖w‖ ^ 2 ≠ 0 := by
    intro h1; apply h0; rw [hiso w wDD, h1, ENNReal.ofReal_zero]
  have hmeas : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      AEStronglyMeasurable (fun y : Mt k r => B (R.σ (Matrix.of y) v)) νq := fun v hv =>
    aesm_of_contOn ((hΦ v (DDsm v hv)).comp hof.continuousOn fun y hy => hy) hGm hνae
  have hsq : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      Integrable (fun y : Mt k r => ‖B (R.σ (Matrix.of y) v)‖ ^ 2) νq ∧
        ∫ y : Mt k r, ‖B (R.σ (Matrix.of y) v)‖ ^ 2 ∂νq = c * ‖v‖ ^ 2 := fun v hv =>
    sq_int (hmeas v hv) (by positivity) (hiso v hv)

  have hpair : ∀ a ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, ∀ b ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      Integrable (fun y : Mt k r => ⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ) νq ∧
      ∫ y : Mt k r, ‖⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ‖ ∂νq ≤ c * ‖a‖ ^ 2 + c * ‖b‖ ^ 2 ∧
      (∫ y : Mt k r, ⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ ∂νq).re = c * (⟪a, b⟫_ℂ).re := by
    intro a ha b hb
    obtain ⟨i1, i2, i3⟩ := inner_int (hmeas a ha) (hmeas b hb) (hsq a ha).1 (hsq b hb).1
    have e : ∫ y : Mt k r, ‖B (R.σ (Matrix.of y) a) + B (R.σ (Matrix.of y) b)‖ ^ 2 ∂νq = c * ‖a + b‖ ^ 2 := by
      rw [← (hsq (a + b) (Submodule.add_mem _ ha hb)).2]
      apply integral_congr_ae
      filter_upwards [hνae] with y hy
      rw [map_add, hB.1 _ (hsm _ hy a (DDsm a ha)) _ (hsm _ hy b (DDsm b hb))]
    rw [(hsq a ha).2, (hsq b hb).2] at i2 i3
    rw [e, norm_add_sq (𝕜 := ℂ)] at i3
    refine ⟨i1, i2, ?_⟩
    simp only [RCLike.re_to_complex] at i3
    linarith

  set m : Mt k r → ℂ := fun g => ⟪w, R.σ (Matrix.of g) w⟫_ℂ with hm
  have hmc : ContinuousOn m {y : Mt k r | Matrix.of y ∈ GG k r} :=
    continuousOn_const.inner ((hcont w).comp hof.continuousOn fun y hy => hy)
  have hmi : Integrable m μG := by
    obtain ⟨C, Ws, -, hd⟩ := GlobalTheory.BesselDecay.decay_TK hy k r ε mu h R hR hgap hok w hwT
    obtain ⟨-, -, t1, t2⟩ := GlobalTheory.thresholds_of_gapOK k r h hok
    have hg := GlobalTheory.gN_rpow_neg_integrable_haar k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hGh (by linarith)
    refine (hg.const_mul (C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum)).mono'
      (aesm_of_contOn hmc hGm hGae) ?_
    filter_upwards [hGae] with y hy
    rw [neg_sub]
    exact hd w hw _ hy

  set F : Mt k r × Mt k r → ℂ := fun q =>
    star (m q.1) * ⟪B (R.σ (Matrix.of q.2) w), B (R.σ (Matrix.of q.2 * Matrix.of q.1) w)⟫_ℂ with hF
  have hFm : AEStronglyMeasurable F (μG.prod νq) := by
    have c1 : Continuous (fun q : Mt k r × Mt k r => (Matrix.of q.1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_fst
    have c2 : Continuous (fun q : Mt k r × Mt k r => (Matrix.of q.2 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_snd
    refine aesm_of_contOn (s := {q : Mt k r × Mt k r | Matrix.of q.1 ∈ GG k r ∧ Matrix.of q.2 ∈ GG k r}) ?_
      ((isClosed_UH.preimage c1).inter (isClosed_UH.preimage c2)).measurableSet
      ((Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hνae))
    exact (continuous_star.comp_continuousOn (hmc.comp continuous_fst.continuousOn fun q hq => hq.1)).mul
      (((hΦ w hw).comp c2.continuousOn fun q hq => hq.2).inner
        ((hΦ w hw).comp (c2.matrix_mul c1).continuousOn fun q hq => Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hq.2 hq.1))
  have hF1 : ∀ g : Mt k r, Matrix.of g ∈ GG k r → (fun y => F (g, y)) =ᵐ[νq] fun y =>
      star (m g) * ⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ := by
    intro g hg
    filter_upwards [hνae] with y hy
    simp only [hF]
    rw [hmul _ hy _ hg]
  have hF2 : ∀ g : Mt k r, Matrix.of g ∈ GG k r → (fun y => F (g, y)) =ᵐ[νq] fun y =>
      ⟪B (R.σ (Matrix.of y) (m g • w)), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ := by
    intro g hg
    filter_upwards [hνae, hF1 g hg] with y hy h1
    rw [h1, map_smul, hB.2.1 _ _ (hsm _ hy w hw), inner_smul_left]
    rfl
  have hFi : Integrable F (μG.prod νq) := by
    rw [integrable_prod_iff hFm]
    constructor
    · filter_upwards [hGae] with g hg
      exact ((hpair w wDD _ (memDD _ hg)).1.const_mul _).congr (hF1 g hg).symm
    · refine (hmi.norm.mul_const (c * ‖w‖ ^ 2 + c * ‖w‖ ^ 2)).mono' hFm.norm.integral_prod_right' ?_
      filter_upwards [hGae] with g hg
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      have e : ∫ y, ‖F (g, y)‖ ∂νq = ‖m g‖ *
          ∫ y : Mt k r, ‖⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ‖ ∂νq := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hF1 g hg] with y hy
        rw [hy, norm_mul, norm_star]
      rw [e]
      have := (hpair w wDD _ (memDD _ hg)).2.1
      rw [hnorm _ hg] at this
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

  have hzero : ∫ q, F q ∂(μG.prod νq) = 0 := by
    rw [integral_prod_symm F hFi]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hνae, hFi.prod_left_ae] with y hy hi
    set f : Mt k r → ℂ := fun g => star ⟪R.σ (Matrix.of y) w, R.σ (Matrix.of g) w⟫_ℂ *
      ⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of g) w)⟫_ℂ with hf
    have hfc : ContinuousOn f {y : Mt k r | Matrix.of y ∈ GG k r} :=
      (continuous_star.comp_continuousOn (continuousOn_const.inner
        ((hcont w).comp hof.continuousOn fun y hy => hy))).mul
        (continuousOn_const.inner ((hΦ w hw).comp hof.continuousOn fun y hy => hy))
    have hfm : AEStronglyMeasurable f (μG.map (lmulM (Matrix.of y))) := by
      rw [hGh.2.2.2 _ hy]; exact aesm_of_contOn hfc hGm hGae
    have hlm : Measurable (lmulM (k := k) (r := r) (Matrix.of y)) :=
      measurable_mulMt.comp (measurable_const.prodMk measurable_id : Measurable fun x : Mt k r => (y, x))
    have e : (fun g => F (g, y)) =ᵐ[μG] f ∘ lmulM (Matrix.of y) := by
      filter_upwards [hGae] with g hg
      show star ⟪w, R.σ (Matrix.of g) w⟫_ℂ * _ = star ⟪R.σ (Matrix.of y) w, R.σ (Matrix.of y * Matrix.of g) w⟫_ℂ * _
      rw [hmul _ hy _ hg w, hun _ hy, ← hmul _ hy _ hg w]
      rfl
    have hfi : Integrable f μG := by
      rw [← hGh.2.2.2 _ hy]
      exact (integrable_map_measure hfm hlm.aemeasurable).2 (hi.congr e)
    have e2 : ∫ g, F (g, y) ∂μG = ∫ g, f g ∂μG := by
      rw [integral_congr_ae e]
      conv_rhs => rw [← hGh.2.2.2 _ hy]
      exact (integral_map hlm.aemeasurable hfm).symm
    rw [e2]
    refine unfold_zero hK hR hS hB hw (fun x hx => ?_) _ hfi
    obtain ⟨j1, j2⟩ := hl.2 x hx _ (hTKs _ hy w hwT)
    refine ⟨j1, ?_⟩
    rw [j2, hcon x hx]
    ext ξ; simp

  obtain ⟨d, hd, hSch⟩ := GlobalTheory.BesselDegree.schur_fdeg hy k r ε μG hGh
  obtain ⟨s1, s2⟩ := (hSch mu R hR).2 w w w w
  have hdpos : 0 < d * fdegHC mu := mul_pos hd (GlobalTheory.BesselNorm.fdegHC_pos mu hR.1.1.injective)
  have hre : (∫ q, F q ∂(μG.prod νq)).re = c * (∫ g, m g * star (m g) ∂μG).re := by
    rw [integral_prod F hFi]
    have a1 := integral_re hFi.integral_prod_left
    have a2 := integral_re s1
    simp only [RCLike.re_to_complex] at a1 a2
    rw [← a1, ← a2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hGae] with g hg
    rw [integral_congr_ae (hF2 g hg), (hpair _ (Submodule.smul_mem _ _ wDD) _ (memDD _ hg)).2.2, inner_smul_left,
      mul_comm ((starRingEnd ℂ) (m g))]
    rfl
  rw [hzero, s2, inner_self_eq_norm_sq_to_K] at hre
  have e3 : (((‖w‖ : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / ((d * fdegHC mu : ℝ) : ℂ))).re =
      ‖w‖ ^ 2 * ‖w‖ ^ 2 / (d * fdegHC mu) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre' : 0 = c * (‖w‖ ^ 2 * ‖w‖ ^ 2 / (d * fdegHC mu)) := by rw [← e3]; exact hre
  have hw2 : ‖w‖ ^ 2 ≠ 0 := right_ne_zero_of_mul hcw
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcw
  exact mul_ne_zero hc0 (div_ne_zero (mul_ne_zero hw2 hw2) hdpos.ne') hre'.symm

theorem exists_kFin_period_ne_zero : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B l : R.H → Wp) (w : R.H), R.IsDS ε mu → GapAtLeast ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → SideG k r z π u μW μN μG νq → IsBes R z π B → R.KFin w → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0 → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → IsBeL R z π μW μN l → ∃ v, R.KFin v ∧ l v ≠ 0 := by
  intro hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq B l w hR hgap hok hS hB hwK h0 hfin hl
  have hK : PI.KFinSmooth := hy.1.2.2.1
  have hw : w ∈ R.sm := hK k r ε mu R.H R.σ hR.1 hR.2 w hwK
  obtain ⟨c, hc, hiso⟩ := GlobalTheory.T.exists_l2SG_translates_eq_const_mul_norm_sq k r ε mu R Wp z π u μW μN μG νq B w hR hS hB hw hfin
  exact GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r ε mu R hR Wp l hl.1.1 hl.1.2.1 hl.1.2.2.2
    (nzOn_of_mass hy hR hgap hok hS hB hwK hc hiso h0 hl)

end GlobalTheory.BesselPeriodNonzero
