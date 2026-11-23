import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerOfNormEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWContinuousUnitaryIrreducible
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaarStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

noncomputable section

namespace GlobalTheory.BesselIsometry

section L2

open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal

variable {X V : Type} [MeasurableSpace X] {ν : Measure X} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem continuous_Lp_two_of_const_norm_pointwise_continuous {ι : Type} [TopologicalSpace ι] [FirstCountableTopology ι] (F : ι → Lp V 2 ν) (f : ι → X → V)
    (hF : ∀ i, (F i : X → V) =ᵐ[ν] f i) (hn : ∀ i j, ‖F i‖ = ‖F j‖) (hc : ∀ᵐ x ∂ν, Continuous fun i => f i x) :
    Continuous F := by
  refine continuous_iff_continuousAt.2 fun j => Metric.tendsto_nhds.2 fun δ hδ => ?_
  by_contra hne
  have hfr : ∃ᶠ i in 𝓝 j, δ ≤ ‖F i - F j‖ := by
    simpa only [not_eventually, not_lt, dist_eq_norm] using hne
  haveI : NeBot (𝓝 j ⊓ 𝓟 {i | δ ≤ ‖F i - F j‖}) := frequently_iff_neBot.1 hfr
  have hb : ∀ i, δ ≤ ‖F i - F j‖ → ‖F i + F j‖ ^ 2 ≤ 4 * ‖F j‖ ^ 2 - δ ^ 2 := fun i hi => by
    have h1 := parallelogram_law_with_norm ℂ (F i) (F j)
    rw [hn i j] at h1
    nlinarith
  have he : ∀ i, (F i + F j : Lp V 2 ν) =ᵐ[ν] fun x => f i x + f j x := fun i => by
    filter_upwards [Lp.coeFn_add (F i) (F j), hF i, hF j] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  have hE : ∀ i, eLpNorm (fun x => f i x + f j x) 2 ν = ENNReal.ofReal ‖F i + F j‖ := fun i => by
    rw [← eLpNorm_congr_ae (he i), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  have h1 := Lp.eLpNorm_le_of_ae_tendsto (u := 𝓝 j ⊓ 𝓟 {i | δ ≤ ‖F i - F j‖}) (f := fun i x => f i x + f j x)
    (g := fun x => f j x + f j x) (p := 2) (μ := ν) (C := ENNReal.ofReal √(4 * ‖F j‖ ^ 2 - δ ^ 2))
    (by
      filter_upwards [mem_inf_of_right (mem_principal_self _)] with i hi
      rw [hE]
      exact ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le (hb i hi)))
    (fun i => (Lp.aestronglyMeasurable _).congr (he i))
    (hc.mono fun x hx => ((hx.tendsto j).add_const _).mono_left inf_le_left)
  rw [hE, ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _), ← two_smul ℂ, norm_smul] at h1
  obtain ⟨i, hi⟩ := hfr.exists
  have h2 := (sq_nonneg _).trans (hb i hi)
  have h3 := pow_le_pow_left₀ (by positivity) h1 2
  rw [Real.sq_sqrt h2] at h3
  simp only [Complex.norm_ofNat] at h3
  nlinarith

theorem integral_norm_inner_le (f g : Lp V 2 ν) : ∫ x, ‖⟪f x, g x⟫_ℂ‖ ∂ν ≤ ‖f‖ * ‖g‖ := by
  have hf := (Lp.memLp f).norm
  have hg := (Lp.memLp g).norm
  have e : ⟪hf.toLp _, hg.toLp _⟫_ℝ = ∫ x, ‖f x‖ * ‖g x‖ ∂ν := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have h1 := real_inner_le_norm (hf.toLp _) (hg.toLp _)
  rw [e, Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm, eLpNorm_norm, ← Lp.norm_def, ← Lp.norm_def] at h1
  refine le_trans (integral_mono (L2.integrable_inner (𝕜 := ℂ) f g).norm (hf.integrable_mul hg)
    fun x => norm_inner_le_norm _ _) h1

end L2

section Closable

open Formalism.MainNotions.S GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped InnerProductSpace Topology ENNReal

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {X V : Type} [MeasurableSpace X] {ν : Measure X} [SigmaFinite ν]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem closable (hσ : IsURepOn (UJset ε) σ) (D : Submodule ℂ H) (a : H →ₗ[ℂ] (X → V)) (A : H →ₗ[ℂ] Lp V 2 ν)
    (hD : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, σ (umat g) v ∈ D) (hA : ∀ v ∈ D, (A v : X → V) =ᵐ[ν] a v)
    (hn : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, ‖A (σ (umat g) v)‖ = ‖A v‖)
    (hm : ∀ v ∈ D, AEStronglyMeasurable (fun p : Formalism.REAL.UJ ε × X => a (σ (umat p.1) v) p.2)
      ((Formalism.REAL.muG ε).prod ν))
    (hp : ∀ᵐ x ∂ν, (∀ v ∈ D, Continuous fun g : Formalism.REAL.UJ ε => a (σ (umat g) v) x) ∧
      ∀ (ξ : V) φ, IsTest φ → (∃ C : ℝ, ∀ w, ‖⟪ξ, a (gard ε σ φ w) x⟫_ℂ‖ ≤ C * ‖w‖) ∧
        ∀ v ∈ D, ⟪ξ, a (gard ε σ φ v) x⟫_ℂ =
          ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪ξ, a (σ (umat g) v) x⟫_ℂ ∂(Formalism.REAL.muG ε))
    (u : ℕ → H) (f : Lp V 2 ν) (hu : ∀ i, u i ∈ D) (hu0 : Tendsto u atTop (𝓝 0))
    (hf : Tendsto (fun i => A (u i)) atTop (𝓝 f)) : f = 0 := by
  have hemb := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Formalism.REAL.UJ ε) := hemb.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Formalism.REAL.UJ ε) := hemb.locallyCompactSpace
  haveI : SigmaFinite (Formalism.REAL.muG ε) := inferInstance
  have hmul : ∀ (g : Formalism.REAL.UJ ε) (v : H), σ (umat g) (σ (umat g⁻¹) v) = v := by
    intro g v
    have e : σ (umat g * umat g⁻¹) = _ := hσ.1.2 _ g.2 _ (g⁻¹).2
    have e1 : umat g * umat g⁻¹ = 1 := Units.mul_inv g.1
    rw [e1, hσ.1.1] at e
    exact (congrArg (fun T : H →L[ℂ] H => T v) e).symm
  have h1 : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, ∀ w ∈ D, ⟪A (σ (umat g) v), A (σ (umat g) w)⟫_ℂ = ⟪A v, A w⟫_ℂ := by
    intro g v hv w hw
    rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
    simp only [← map_smul, ← map_add, ← map_sub]
    rw [hn g _ (D.add_mem hv hw), hn g _ (D.sub_mem hv hw), hn g _ (D.sub_mem hv (D.smul_mem _ hw)),
      hn g _ (D.add_mem hv (D.smul_mem _ hw))]
  have key : ∀ v ∈ D, ⟪A v, f⟫_ℂ = 0 := by
    intro v hv
    have hcA : Continuous fun g : Formalism.REAL.UJ ε => A (σ (umat g) v) :=
      continuous_Lp_two_of_const_norm_pointwise_continuous _ (fun g => a (σ (umat g) v)) (fun g => hA _ (hD g v hv))
        (fun g g' => by rw [hn g v hv, hn g' v hv]) (hp.mono fun x hx => hx.1 v hv)
    have hc : ∀ y : Lp V 2 ν, Continuous fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), y⟫_ℂ := fun y =>
      (hcA.comp continuous_inv).inner continuous_const
    have h0 := eq_zero_of_forall_test (F := fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), f⟫_ℂ) (hc f) (by
      intro φ hφ
      have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) (Formalism.REAL.muG ε) := by
        simpa using hφ.integrable (F := fun _ : Formalism.REAL.UJ ε => (1 : ℝ)) continuous_const
      set c : ℝ := (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε)) * ‖A v‖ with hcdef
      let p : H → X → ℂ := fun w x => ⟪A v x, a (gard ε σ φ w) x⟫_ℂ
      have hP : ∀ w ∈ D, Integrable (p w) ν ∧ ∫ x, ‖p w x‖ ∂ν ≤ c * ‖A w‖ ∧
          ∫ x, p w x ∂ν = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), A w⟫_ℂ ∂(Formalism.REAL.muG ε) := by
        intro w hw
        let K : Formalism.REAL.UJ ε × X → ℂ := fun q => φ (umat q.1) • ⟪A v q.2, a (σ (umat q.1) w) q.2⟫_ℂ
        have hKm : AEStronglyMeasurable K ((Formalism.REAL.muG ε).prod ν) :=
          hψi.aestronglyMeasurable.comp_fst.smul ((Lp.aestronglyMeasurable (A v)).comp_snd.inner (hm w hw))
        have hae : ∀ g : Formalism.REAL.UJ ε, (fun x => ⟪A v x, A (σ (umat g) w) x⟫_ℂ) =ᵐ[ν]
            fun x => ⟪A v x, a (σ (umat g) w) x⟫_ℂ := fun g => (hA _ (hD g w hw)).mono fun x hx => by simp only [hx]
        have hKb : ∀ g : Formalism.REAL.UJ ε, ∫ x, ‖K (g, x)‖ ∂ν ≤ ‖φ (umat g)‖ * (‖A v‖ * ‖A w‖) := fun g => by
          simp only [K, norm_smul, integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [← hn g w hw]
          refine le_trans (le_of_eq (integral_congr_ae ?_)) (integral_norm_inner_le _ _)
          exact (hae g).mono fun x hx => congrArg norm hx.symm
        have hK : Integrable K ((Formalism.REAL.muG ε).prod ν) := by
          rw [integrable_prod_iff hKm]
          refine ⟨Eventually.of_forall fun g => ((L2.integrable_inner (𝕜 := ℂ) _ _).congr (hae g)).smul (φ (umat g)),
            Integrable.mono' (hψi.norm.mul_const (‖A v‖ * ‖A w‖)) hKm.norm.integral_prod_right'
              (Eventually.of_forall fun g => ?_)⟩
          rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
          exact hKb g
        have e : p w =ᵐ[ν] fun x => ∫ g, K (g, x) ∂(Formalism.REAL.muG ε) := hp.mono fun x hx => (hx.2 _ φ hφ).2 w hw
        refine ⟨hK.integral_prod_right.congr e.symm, ?_, ?_⟩
        · calc ∫ x, ‖p w x‖ ∂ν = ∫ x, ‖∫ g, K (g, x) ∂(Formalism.REAL.muG ε)‖ ∂ν :=
                integral_congr_ae (e.mono fun x hx => congrArg norm hx)
            _ ≤ ∫ x, ∫ g, ‖K (g, x)‖ ∂(Formalism.REAL.muG ε) ∂ν :=
                integral_mono hK.integral_prod_right.norm hK.integral_norm_prod_right
                  fun x => norm_integral_le_integral_norm _
            _ = ∫ g, ∫ x, ‖K (g, x)‖ ∂ν ∂(Formalism.REAL.muG ε) :=
                (integral_integral_swap (f := fun g x => ‖K (g, x)‖) hK.norm).symm
            _ ≤ ∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ * (‖A v‖ * ‖A w‖) ∂(Formalism.REAL.muG ε) :=
                integral_mono hK.integral_norm_prod_left (hψi.norm.mul_const _) hKb
            _ = c * ‖A w‖ := by rw [integral_mul_const, hcdef, mul_assoc]
        · rw [integral_congr_ae e, ← integral_integral_swap (f := fun g x => K (g, x)) hK]
          congr 1
          funext g
          simp only [K]
          rw [integral_smul, ← integral_congr_ae (hae g), ← L2.inner_def, ← h1 g _ (hD g⁻¹ v hv) w hw, hmul]
      have hsub : ∀ w w' x, p (w - w') x = p w x - p w' x := fun w w' x => by
        simp only [p, gard_eq hσ hφ, map_sub, Pi.sub_apply, inner_sub_right]
      have hlim : ∀ᵐ x ∂ν, Tendsto (fun i => p (u i) x) atTop (𝓝 0) := hp.mono fun x hx => by
        obtain ⟨C, hC⟩ := (hx.2 (A v x) φ hφ).1
        refine squeeze_zero_norm (fun i => hC (u i)) ?_
        simpa using hu0.norm.const_mul C
      have hfat : ∀ i, ∫ x, ‖p (u i) x‖ ∂ν ≤ c * ‖A (u i) - f‖ := fun i => by
        have h2 := Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := ν) (p := 1) (f := fun j => p (u i - u j))
          (fun j => (hP _ (D.sub_mem (hu i) (hu j))).1.aestronglyMeasurable) (p (u i))
          (hlim.mono fun x hx => by simpa only [hsub, sub_zero] using hx.const_sub (p (u i) x))
        simp only [eLpNorm_one_eq_lintegral_enorm] at h2
        have h3 : Tendsto (fun j => ENNReal.ofReal (c * ‖A (u i - u j)‖)) atTop
            (𝓝 (ENNReal.ofReal (c * ‖A (u i) - f‖))) := by
          simp only [map_sub]
          exact ENNReal.tendsto_ofReal ((hf.const_sub _).norm.const_mul c)
        have h4 := h2.trans ((liminf_le_liminf (Eventually.of_forall fun j => by
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hP _ (D.sub_mem (hu i) (hu j))).1]
          exact ENNReal.ofReal_le_ofReal (hP _ (D.sub_mem (hu i) (hu j))).2.1)).trans h3.liminf_eq.le)
        rwa [← ofReal_integral_norm_eq_lintegral_enorm (hP _ (hu i)).1, ENNReal.ofReal_le_ofReal_iff
          (mul_nonneg (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))] at h4
      have t3 : Tendsto (fun i => c * ‖A (u i) - f‖) atTop (𝓝 0) := by
        simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hf).const_mul c
      have t1 : Tendsto (fun i => ∫ x, p (u i) x ∂ν) atTop (𝓝 0) :=
        squeeze_zero_norm (fun i => (norm_integral_le_integral_norm _).trans (hfat i)) t3
      have t2 : Tendsto (fun i => ∫ x, p (u i) x ∂ν) atTop
          (𝓝 (∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), f⟫_ℂ ∂(Formalism.REAL.muG ε))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) t3
        rw [(hP _ (hu i)).2.2, ← integral_sub (hφ.integrable (hc _)) (hφ.integrable (hc _)), hcdef, mul_assoc,
          ← integral_mul_const]
        refine norm_integral_le_of_norm_le (hψi.norm.mul_const _) (Eventually.of_forall fun g => ?_)
        rw [← smul_sub, norm_smul, ← inner_sub_right, ← hn g⁻¹ v hv]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      exact tendsto_nhds_unique t2 t1)
    have e : σ (umat (1 : Formalism.REAL.UJ ε)⁻¹) v = v := by
      rw [inv_one]
      show σ 1 v = v
      rw [hσ.1.1]; rfl
    simpa only [e] using h0
  have t := hf.inner (𝕜 := ℂ) (tendsto_const_nhds (x := f))
  simp only [key _ (hu _)] at t
  exact inner_self_eq_zero.1 (tendsto_nhds_unique t tendsto_const_nhds)

end Closable

section Quot

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

variable {k r : ℕ}

theorem sigmaFinite_of_quot {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μG] [SFinite μS] (hS : μS ≠ 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨f, hpos, hf, hlt⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hc : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt k r) :=
    Continuous.matrix_mul (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (A := fun p => (Matrix.of p.2 : Mx k r))
      (B := fun p => (Matrix.of p.1 : Mx k r)) continuous_snd continuous_fst
  have hm := hf.coe_nnreal_ennreal.comp hc.measurable
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    fun x => ∫⁻ s, (f (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS with hF
  have hFm : Measurable F := hm.lintegral_prod_right'
  have hFi : ∫⁻ x, F x ∂ν ≠ ⊤ := by
    rw [← hq _ hf.coe_nnreal_ennreal]
    exact (hlt.trans ENNReal.one_lt_top).ne
  have hFp : ∀ x, F x ≠ 0 := fun x h0 => by
    have h1 := (lintegral_eq_zero_iff (hm.comp (measurable_prodMk_left (x := x)))).1 h0
    haveI : NeZero μS := ⟨hS⟩
    obtain ⟨s, hs⟩ := h1.exists
    exact (hpos _).ne' (ENNReal.coe_eq_zero.1 hs)
  refine ⟨⟨⟨fun m => {x | ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ F x}, fun _ => trivial, fun m => ?_, ?_⟩⟩⟩
  · exact (meas_ge_le_lintegral_div hFm.aemeasurable (by simp) (by simp)).trans_lt
      (ENNReal.div_lt_top hFi (by simp))
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt (hFp x)
    exact Set.mem_iUnion.2 ⟨m, le_trans (ENNReal.inv_le_inv.2 (by simp)) hm.le⟩

theorem quotientMass_right_translation_invariant {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) {Φ : Mx k r → Wp}
    (hΦ : ContinuousOn Φ (GG k r)) (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, ‖Φ (s * x)‖ = ‖Φ x‖)
    {g : Mx k r} (hg : g ∈ GG k r) :
    PI.BesselPeriodGGP.l2SG νq (fun x => Φ (x * g)) = PI.BesselPeriodGGP.l2SG νq Φ := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  have hae := GlobalTheory.QuotRightInv.ae_mem_of_quot hset
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := IsClosed.measurableSet (α := Formalism.QuantumDeterminants.Mt k r) hGG.1
  have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => ‖Φ (Matrix.of x)‖₊) A := hΦ.nnnorm
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ‖Φ (Matrix.of x)‖₊) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ‖Φ (Matrix.of x)‖₊) (fun _ => 0) x = ‖Φ (Matrix.of x)‖₊ :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ (hm.coe_nnreal_ennreal.pow_const 2) (fun s hs x hx => by
    rw [hval x hx, hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)]
    congr 2
    exact NNReal.eq (hinv s hs _ hx)) g hg
  unfold PI.BesselPeriodGGP.l2SG
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => ?_)))
  · simp only
    rw [hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)]
    rfl
  · simp only
    rw [hval x hx]

open GlobalTheory.CWDeriv in

theorem continuousOn_orbit {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDS ε mu) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Bm : R.H → V}
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v)
    (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm) {v : R.H} (hv : v ∈ R.sm) :
    ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) := by
  have hD : DerFacts R := fun X hX =>
    ⟨fun _ hv => ⟨GlobalTheory.DerivedAction.dsig_smooth hR.2 hX hv, GlobalTheory.DerivedAction.hasDerivAt_dsig hX hv⟩,
      fun _ hv _ hw => GlobalTheory.DerivedAction.dsig_skew hR.2 hX hv hw⟩
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hB0 : Bm 0 = 0 := by simpa using hs 0 0 h0
  intro g hg
  have h1 := cw_tendsto hB (l := 𝓝[GG k r] g) (u := fun x => (1 : ℂ) • (R.σ x v - R.σ g v) - 0)
    (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact sm_comb 1 (hsm x hx) (hsm g hg) h0)
    (by
      intro W hW
      have h2 := (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW) g hg).tendsto
      have hW0 : PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0 = 0 := by
        have h := dsigW_comb hD W hW 0 h0 h0 h0
        simp only [zero_smul, zero_sub, neg_zero] at h
        rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h
        simpa using h
      rw [← tendsto_sub_nhds_zero_iff] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [dsigW_comb hD W hW 1 (hsm x hx) (hsm g hg) h0, hW0, one_smul, sub_zero])
  refine tendsto_sub_nhds_zero_iff.mp (h1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [lin_comb ha hs 1 (hsm x hx) (hsm g hg) h0, hB0, one_smul, sub_zero]

end Quot

theorem quotientMass_eq_eLpNorm_sq {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r))
    (Φ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → Wp) :
    PI.BesselPeriodGGP.l2SG ν Φ = MeasureTheory.eLpNorm (fun x : Formalism.QuantumDeterminants.Mt k r => Φ (Matrix.of x)) 2 ν ^ 2 := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := ν) (p := 2)
    (f := fun x : Formalism.QuantumDeterminants.Mt k r => Φ (Matrix.of x)) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.rpow_ofNat, ENNReal.coe_ofNat] at h
  exact h.symm

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem besselQuotientMass_eq_const_mul_norm_sq_translates : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B : R.H → Wp) (w : R.H), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π B → w ∈ R.sm → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → ∃ c : ℝ, 0 ≤ c ∧ ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = ENNReal.ofReal (c * ‖v‖ ^ 2) := by
  intro k r ε mu R Wp _ _ _ _ z π u μW μN μG νq B w hR hS hB hw hfin
  obtain ⟨-, hσ, -⟩ := GlobalTheory.BesselMapOne.rep_of_isDSHpk hR.2
  obtain ⟨P, ⟨⟨hP, hG⟩, -⟩, -, -, hU, hI, -⟩ := hR.2
  set σ' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (R.H →L[ℂ] R.H) := fun g => R.σ (P⁻¹ * g * P)
    with hσ'
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have e : GlobalTheory.SmVec.trRep σ' P = R.σ := funext fun g => by
    unfold GlobalTheory.SmVec.trRep
    simp only [hσ']
    congr 1
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.mul_one]
  have hs : ∀ v, v ∈ R.sm ↔ v ∈ GlobalTheory.SmVec.smSub (Hpk k r) R.σ :=
    GlobalTheory.BesselMapOne.smoothOnH_iff_mem (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r) (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r) hσ
  have hGu : IsUnit (Hpk k r) := GlobalTheory.SmVec.gram_unit hP hG
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2
  obtain ⟨hGG, -⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  have hconj : ∀ g : Formalism.REAL.UJ ε, P⁻¹ * umat g * P ∈ BranchingSupport.GG k r := fun g => GlobalTheory.SmVec.conj_mem_UH hP hG g.2
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v, R.σ g (R.σ h v) = R.σ (g * h) v := fun g hg h hh v =>
    (GlobalTheory.SmVec.rep_mul hσ hg hh v).symm
  have hS' := hS
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, hHG, hq⟩ := hS'
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae : ∀ᵐ x ∂νq, Matrix.of x ∈ BranchingSupport.GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hHG.2.2.1 h0 h1 hq
  haveI := hHG.1
  haveI := (GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN).2.2.1.1
  haveI : SigmaFinite νq := sigmaFinite_of_quot h0 hq
  haveI : SecondCountableTopology Wp := by
    haveI : ProperSpace Wp := FiniteDimensional.proper ℂ Wp
    infer_instance
  have hπu := (GlobalTheory.ThA.hcType_rep k r z u₀ Wp π hz hT hπ).2.2.2.1
  let L : R.smSub →ₗ[ℂ] Wp :=
    { toFun := fun x => B x
      map_add' := fun x y => hB.1 _ x.2 _ y.2
      map_smul' := fun c x => hB.2.1 c _ x.2 }
  obtain ⟨Bl, hBl⟩ := L.exists_extend
  have hBl' : ∀ v ∈ R.sm, Bl v = B v := fun v hv => LinearMap.congr_fun hBl ⟨v, hv⟩
  let a : R.H →ₗ[ℂ] (Mt k r → Wp) := LinearMap.pi fun x => Bl ∘ₗ (R.σ (Matrix.of x) : R.H →ₗ[ℂ] R.H)
  have ha : ∀ v ∈ R.sm, ∀ x : Mt k r, Matrix.of x ∈ BranchingSupport.GG k r → a v x = B (R.σ (Matrix.of x) v) :=
    fun v hv x hx => hBl' _ (hsm v hv _ hx)
  have hcont : ∀ v ∈ R.sm, ContinuousOn (fun g => B (R.σ g v)) (BranchingSupport.GG k r) := fun v hv =>
    continuousOn_orbit hR hB.1 hB.2.1 hB.2.2.2 hv
  have hl2 : ∀ v ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = eLpNorm (a v) 2 νq ^ 2 := fun v hv => by
    rw [quotientMass_eq_eLpNorm_sq, eLpNorm_congr_ae (hae.mono fun x hx => ha v hv x hx)]
  have hinv : ∀ v ∈ R.sm, ∀ g ∈ BranchingSupport.GG k r, eLpNorm (a (R.σ g v)) 2 νq = eLpNorm (a v) 2 νq := fun v hv g hg => by
    have h2 := quotientMass_right_translation_invariant hS (hcont v hv) (by
      rintro _ ⟨h, hh, m, hm, rfl⟩ x hx
      rw [← hmul _ (hGG.2.2.1 _ hh.1 _ hm.1) _ hx, hB.2.2.1 h hh m hm _ (hsm v hv x hx), norm_smul, hπu h hh]
      simp [Formalism.QuantumDeterminants.psi, Complex.norm_exp]) hg
    have h3 : PI.BesselPeriodGGP.l2SG νq (fun x => B (R.σ x (R.σ g v))) =
        PI.BesselPeriodGGP.l2SG νq (fun x => B (R.σ (x * g) v)) :=
      lintegral_congr_ae (hae.mono fun x hx => by simp only [hmul _ hx _ hg])
    rw [← h3, hl2 _ (hsm v hv g hg), hl2 v hv] at h2
    exact (ENNReal.pow_right_strictMono two_ne_zero).injective h2
  have hAm : MeasurableSet {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r} := IsClosed.measurableSet (α := Mt k r) hGG.1
  have hmeas : ∀ v ∈ R.sm, AEStronglyMeasurable (a v) νq := fun v hv => by
    have hc : ContinuousOn (fun x : Mt k r => B (R.σ (Matrix.of x) v)) {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r} :=
      hcont v hv
    have h2 := hc.aestronglyMeasurable (μ := νq) hAm
    rw [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r}) hae] at h2
    exact h2.congr (hae.mono fun x hx => (ha v hv x hx).symm)
  set D := Formalism.FourierDecayAlt.ThreeDimData.DDsp (k := k) (r := r) R.σ w with hDdef
  have hDs : ∀ v ∈ D, v ∈ R.sm := fun v hv =>
    (Submodule.span_le (p := R.smSub)).2 (by rintro _ ⟨g, hg, rfl⟩; exact hsm w hw g hg) hv
  have hDst : ∀ g ∈ BranchingSupport.GG k r, ∀ v ∈ D, R.σ g v ∈ D := fun g hg v hv =>
    (Submodule.span_le (p := D.comap (R.σ g : R.H →ₗ[ℂ] R.H))).2 (by
      rintro _ ⟨h, hh, rfl⟩
      exact Submodule.subset_span ⟨g * h, hGG.2.2.1 _ hg _ hh, (hmul g hg h hh w).symm⟩) hv
  have hmem : ∀ v ∈ D, MemLp (a v) 2 νq := fun v hv => by
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, hg, rfl⟩ := hy
      refine ⟨hmeas _ (hsm w hw g hg), ?_⟩
      rw [hinv w hw g hg]
      rw [hl2 w hw] at hfin
      exact lt_top_iff_ne_top.2 fun h => hfin (by rw [h]; simp)
    | zero => rw [map_zero]; exact MemLp.zero
    | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
    | smul c x _ hx => rw [map_smul]; exact hx.const_smul c
  let A₀ : D →ₗ[ℂ] Lp Wp 2 νq :=
    { toFun := fun v => (hmem v v.2).toLp _
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        congr 1
        simp
      map_smul' := fun c w => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        congr 1
        simp }
  obtain ⟨A, hA⟩ := A₀.exists_extend
  have hA' : ∀ v (hv : v ∈ D), A v = (hmem v hv).toLp _ := fun v hv => LinearMap.congr_fun hA ⟨v, hv⟩
  have hAn : ∀ v ∈ D, ‖A v‖ = (eLpNorm (a v) 2 νq).toReal := fun v hv => by rw [hA' v hv, Lp.norm_toLp]
  have hD' : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, σ' (umat g) v ∈ D := fun g => hDst _ (hconj g)
  have hn' : ∀ g : Formalism.REAL.UJ ε, ∀ v ∈ D, ‖A (σ' (umat g) v)‖ = ‖A v‖ := fun g v hv => by
    rw [hAn _ (hD' g v hv), hAn v hv]
    exact congrArg _ (hinv v (hDs v hv) _ (hconj g))
  have c1 : Continuous fun g : Formalism.REAL.UJ ε => P⁻¹ * umat g * P :=
    (continuous_const.matrix_mul GlobalTheory.SmVec.continuous_umat).matrix_mul continuous_const
  have hval : ∀ v ∈ D, ∀ (g : Formalism.REAL.UJ ε) (x : Mt k r), Matrix.of x ∈ BranchingSupport.GG k r →
      a (σ' (umat g) v) x = B (R.σ (Matrix.of x * (P⁻¹ * umat g * P)) v) := fun v hv g x hx => by
    rw [ha _ (hDs _ (hD' g v hv)) x hx, ← hmul _ hx _ (hconj g)]
  have hcl := closable (ν := νq) hU D a A hD' (fun v hv => by rw [hA' v hv]; exact (hmem v hv).coeFn_toLp) hn'
    (fun v hv => by
      have hemb := (Formalism.REAL.isClosedEmbeddingMatrix (2 * r + k + 1) ε).1
      haveI : SecondCountableTopology (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
        inferInstanceAs (SecondCountableTopology (Mt k r))
      haveI : SecondCountableTopology (Formalism.REAL.UJ ε) := hemb.isEmbedding.secondCountableTopology
      have hae2 : ∀ᵐ p ∂((Formalism.REAL.muG ε).prod νq), p ∈ Prod.snd ⁻¹' {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r} :=
        Measure.quasiMeasurePreserving_snd.ae hae
      have c2 : Continuous fun p : Formalism.REAL.UJ ε × Mt k r => Matrix.of p.2 * (P⁻¹ * umat p.1 * P) :=
        Continuous.matrix_mul (A := fun p : Formalism.REAL.UJ ε × Mt k r => Matrix.of p.2) continuous_snd
          (c1.comp continuous_fst)
      have hc := (hcont v (hDs v hv)).comp (s := Prod.snd ⁻¹' {x : Mt k r | Matrix.of x ∈ BranchingSupport.GG k r})
        c2.continuousOn (fun p hp => hGG.2.2.1 _ hp _ (hconj p.1))
      have h2 := hc.aestronglyMeasurable (μ := (Formalism.REAL.muG ε).prod νq) (measurable_snd hAm)
      rw [Measure.restrict_eq_self_of_ae_mem hae2] at h2
      exact h2.congr (hae2.mono fun p hp => (hval v hv p.1 p.2 hp).symm))
    (hae.mono fun x hx => ⟨fun v hv => by
        simp only [hval v hv _ x hx]
        exact (hcont v (hDs v hv)).comp_continuous (continuous_const.matrix_mul c1)
          fun g => hGG.2.2.1 _ hx _ (hconj g), fun ξ φ hφ => by
      obtain ⟨C, Ws, hWs, hC⟩ := hB.2.2.2
      have hsob : Formalism.L2.Theta.Sobolev₂ (GlobalTheory.SmVec.lieG (Hpk k r)) (GlobalTheory.SmVec.trRep σ' P)
          ((innerSL ℂ ξ : Wp →ₗ[ℂ] ℂ) ∘ₗ (LinearMap.proj x) ∘ₗ a) := by
        rw [e]
        refine ⟨Ws.map fun l => l.map fun X => (Matrix.of x)⁻¹ * X * Matrix.of x, ‖ξ‖ * C, ?_, fun v hv => ?_⟩
        · intro l hl X hX
          obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
          obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
          exact GlobalTheory.SmVec.conj_mem_lieG hGu hx (hWs l' hl' Y hY)
        · have hv' := (hs v).2 hv
          show ‖⟪ξ, a v x⟫_ℂ‖ ≤ _
          rw [ha v hv' x hx, mul_assoc]
          refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          refine (hC _ (hsm v hv' _ hx)).trans (le_of_eq ?_)
          rw [List.map_map]
          congr 2
          refine List.map_congr_left fun l hl => ?_
          rw [GlobalTheory.BesselMapOne.dsigW_eq]
          exact (congrArg norm (GlobalTheory.SmVec.WordCont.word_rep hGu hσ hv hx (hWs l hl))).trans (hσ.2.1 _ hx _)
      obtain ⟨q1, q2⟩ := GlobalTheory.SobGarding.sobCont_gard _ ε R.H σ' P _ hP hG hU _ hsob
      exact ⟨q1 φ hφ, fun v hv => (q2 v (by rw [e]; exact (hs v).1 (hDs v hv))).2 φ hφ⟩⟩)
  obtain ⟨c, hc⟩ := GlobalTheory.ClosableSchur.norm_sq_eq (Formalism.REAL.UJ ε) R.H (Lp Wp 2 νq) (fun g => σ' (umat g)) D
    (fun g v => hU.2.1 _ g.2 v)
    (fun g => by
      have hm : ∀ (g : Formalism.REAL.UJ ε) (v : R.H), σ' (umat g) (σ' (umat g⁻¹) v) = v := by
        intro g v
        have e : σ' (umat g * umat g⁻¹) = _ := hU.1.2 _ g.2 _ (g⁻¹).2
        have e1 : umat g * umat g⁻¹ = 1 := Units.mul_inv g.1
        have e2 : σ' 1 = 1 := hU.1.1
        rw [e1, e2] at e
        exact (congrArg (fun T : R.H →L[ℂ] R.H => T v) e).symm
      exact ⟨g⁻¹, fun v => by simpa only [inv_inv] using hm g⁻¹ v, hm g⟩)
    (fun S hS h => hI S hS fun g hg v hv => by
      have hu : IsUnit g := GlobalTheory.SmVec.isUnit_of_mem_UH (G := Formalism.REAL.Jm ε)
        (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)) hg
      exact h ⟨hu.unit, hg⟩ v hv)
    hD' A hn' hcl
  refine ⟨max c 0, le_max_right _ _, fun v hv => ?_⟩
  have h2 : max c 0 * ‖v‖ ^ 2 = ‖A v‖ ^ 2 := by
    have h3 := hc v hv
    rcases le_total 0 c with h | h
    · rw [max_eq_left h, h3]
    · rw [max_eq_right h, zero_mul]
      exact le_antisymm (sq_nonneg _) (h3 ▸ mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _))
  rw [h2, hl2 v (hDs v hv), hAn v hv, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (hmem v hv).2.ne]

end GlobalTheory.BesselIsometry

end
