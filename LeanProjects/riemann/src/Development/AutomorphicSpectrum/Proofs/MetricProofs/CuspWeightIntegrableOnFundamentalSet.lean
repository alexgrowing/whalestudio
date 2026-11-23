import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FundamentalSetToFundamentalDomainStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumIntegralBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumContinuousCuspWeightMeasurableStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmFieldSmallIntegralBasisStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBoundsStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallMean

open GroundTheory.Heights₂.Heights.LowerBound

theorem weighted_mean {X : Type} [MeasurableSpace X] (m : Measure X) (S : Set X) (d U lam : X → ℝ) (f j' : ℕ) (vr rd : ℝ)
    (hd : Measurable d) (hdpos : ∀ x, 0 < d x)
    (h0 : ∫⁻ t in S, ENNReal.ofReal (d t) ∂m ≠ 0) (hT : ∫⁻ t in S, ENNReal.ofReal (d t) ∂m ≠ ⊤)
    (U_meas : Measurable U) (lam_meas : Measurable lam) (lam_pos : ∀ z, 0 < lam z) (U_nonneg : ∀ z, 0 ≤ U z)
    (U_le : ∀ z, U z ≤ f * j' * (2 * max 0 (Real.log (1 / lam z)) + Real.log (2 * f * j' * rd)))
    (hf : 1 ≤ f) (hj : 1 ≤ j') (hvr : 1 ≤ vr) (hrd : 1 ≤ rd)
    (mean : ∫⁻ t in S, ENNReal.ofReal (Real.log (vr ^ (-(1 / 2 : ℝ)) / lam t)) * ENNReal.ofReal (d t) ∂m ≤
      3 * ∫⁻ t in S, ENNReal.ofReal (d t) ∂m) :
    IntegrableOn d S m ∧ 0 < ∫ t in S, d t ∂m ∧ IntegrableOn (fun t => U t * d t) S m ∧
      ∫ t in S, U t * d t ∂m ≤
        f * j' * (6 + Real.log vr + Real.log (2 * f * j' * rd)) * ∫ t in S, d t ∂m := by
  set w : X → ℝ≥0∞ := fun t => ENNReal.ofReal (d t) with hw
  have hwm : Measurable w := hd.ennreal_ofReal
  have hwlt : ∀ᵐ x ∂(m.restrict S), w x < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  set V : ℝ≥0∞ := ∫⁻ t in S, w t ∂m with hV
  set ρ : Measure X := (m.restrict S).withDensity w with hρ
  have hρuniv : ρ Set.univ = V := by
    rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  set ν : Measure X := V⁻¹ • ρ with hν
  have hprob : IsProbabilityMeasure ν :=
    ⟨by simp [hν, hρuniv, ENNReal.inv_mul_cancel h0 hT]⟩
  have hinv0 : V⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hT
  have hinvT : V⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  have hdnn : ∀ x, 0 ≤ d x := fun x => (hdpos x).le
  have hwr : ∀ x, (w x).toReal = d x := fun x => ENNReal.toReal_ofReal (hdnn x)

  have hdint : Integrable d (m.restrict S) := by
    refine ⟨hd.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hdnn)]
    exact lt_top_iff_ne_top.2 hT
  have hdval : ∫ t in S, d t ∂m = V.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hdnn) hd.aestronglyMeasurable]
  have hVpos : 0 < V.toReal := ENNReal.toReal_pos h0 hT

  set r : ℝ := vr ^ (-(1 / 2 : ℝ)) with hr
  set L : X → ℝ := fun z => max 0 (Real.log (r / lam z)) with hL
  have hLm : Measurable L := measurable_const.max (Real.measurable_log.comp (lam_meas.const_div r))
  have hLnn : ∀ z, 0 ≤ L z := fun z => le_max_left _ _
  have hLof : ∀ z, ENNReal.ofReal (L z) = ENNReal.ofReal (Real.log (r / lam z)) := fun z => by
    rcases le_total 0 (Real.log (r / lam z)) with h | h
    · simp only [hL, max_eq_right h]
    · simp only [hL, max_eq_left h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have hlin : ∀ g : X → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂ν = V⁻¹ * ∫⁻ x in S, w x * g x ∂m := fun g hg => by
    rw [hν, lintegral_smul_measure, hρ, lintegral_withDensity_eq_lintegral_mul _ hwm hg]
    rfl
  have hLle : ∫⁻ x, ENNReal.ofReal (L x) ∂ν ≤ 3 := by
    rw [hlin _ hLm.ennreal_ofReal]
    have e : ∫⁻ x in S, w x * ENNReal.ofReal (L x) ∂m ≤ 3 * V := by
      refine le_of_eq_of_le (lintegral_congr fun x => ?_) mean
      rw [hLof, mul_comm]
    calc V⁻¹ * ∫⁻ x in S, w x * ENNReal.ofReal (L x) ∂m ≤ V⁻¹ * (3 * V) := by gcongr
      _ = 3 := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel h0 hT, mul_one]
  have hLint : Integrable L ν := by
    refine ⟨hLm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hLnn)]
    exact lt_of_le_of_lt hLle (by simp)
  have hLmean : ∫ z, L z ∂ν ≤ 3 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hLnn) hLm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hLle)
  have H : MeanCuspWeight.Hyp ν U lam f j' vr rd :=
    { isProbability := hprob
      U_meas := U_meas
      lam_meas := lam_meas
      lam_pos := lam_pos
      U_nonneg := U_nonneg
      U_le := U_le
      one_le_f := hf
      one_le_j' := hj
      one_le_vr := hvr
      one_le_rd := hrd
      logPlus_integrable := hLint
      logPlus_mean := hLmean }
  have hbound := MeanCuspWeight.full X ν U lam f j' vr rd H

  have hvr0 : 0 < vr := lt_of_lt_of_le one_pos hvr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hvr0 _
  have hlogvr : 0 ≤ Real.log vr := Real.log_nonneg hvr
  have hlogr : Real.log r = -(1 / 2) * Real.log vr := Real.log_rpow hvr0 _
  have key : ∀ z, max 0 (Real.log (1 / lam z)) ≤ L z + 1 / 2 * Real.log vr := by
    intro z
    have hl := lam_pos z
    have e : Real.log (1 / lam z) = Real.log (r / lam z) + 1 / 2 * Real.log vr := by
      rw [Real.log_div one_ne_zero hl.ne', Real.log_div hr0.ne' hl.ne', hlogr, Real.log_one]
      ring
    refine max_le (by have := hLnn z; positivity) ?_
    rw [e]
    have : Real.log (r / lam z) ≤ L z := le_max_right _ _
    linarith
  have hfj : (0 : ℝ) ≤ (f : ℝ) * j' := by positivity
  have hUint : Integrable U ν := by
    have hg : Integrable (fun z => (f : ℝ) * j' * (2 * (L z + 1 / 2 * Real.log vr) +
        Real.log (2 * f * j' * rd))) ν :=
      (((hLint.add (integrable_const _)).const_mul 2).add (integrable_const _)).const_mul _
    refine hg.mono' U_meas.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (U_nonneg z)]
    refine (U_le z).trans (mul_le_mul_of_nonneg_left ?_ hfj)
    linarith [key z]
  have hUρ : Integrable U ρ := (integrable_smul_measure hinv0 hinvT).1 hUint
  have hUd : Integrable (fun t => U t * d t) (m.restrict S) := by
    have := (integrable_withDensity_iff_integrable_smul' hwm hwlt).1 hUρ
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul, hwr, mul_comm]
  have hval : ∫ z, U z ∂ν = (V.toReal)⁻¹ * ∫ t in S, U t * d t ∂m := by
    rw [hν, integral_smul_measure, hρ, integral_withDensity_eq_integral_toReal_smul hwm hwlt,
      ENNReal.toReal_inv, smul_eq_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul, hwr, mul_comm]
  refine ⟨hdint, by rw [hdval]; exact hVpos, hUd, ?_⟩
  rw [hval, inv_mul_le_iff₀ hVpos] at hbound
  rw [hdval]
  linarith

end GlobalTheory.CompanionTheory.Ar.Cusp.BallMean

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallMean

section Card

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hom_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  have hk : RingHom.ker s = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro m hm
    have h1 : s (algebraMap ℤ (𝓞 E) m) = 0 := hm
    have h2 : ((m : ℤ) : ℂ) = 0 := by simpa using h1
    simpa using (Int.cast_eq_zero.1 h2)
  intro a ha
  have : a ∈ RingHom.ker s := ha
  rw [hk] at this
  simpa using this

theorem finrank_eq_two_mul {Ψ : Type} [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) :
    Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  classical
  let e : (E →+* ℂ) ≃ (𝓞 E →+* ℂ) :=
    { toFun := fun φ => φ.comp (algebraMap (𝓞 E) E)
      invFun := fun s => IsFractionRing.lift (hom_injective s)
      left_inv := fun φ => by
        apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        ext x
        simp
      right_inv := fun s => by
        ext x
        simp }
  haveI : Fintype (𝓞 E →+* ℂ) := Fintype.ofEquiv _ e
  have hc : Fintype.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
    rw [← Fintype.card_congr e]
    exact NumberField.Embeddings.card E ℂ
  let P : (𝓞 E →+* ℂ) → Prop := fun s => ∃ τ, σ τ = s
  let c : (𝓞 E →+* ℂ) → (𝓞 E →+* ℂ) := fun s => (starRingEnd ℂ).comp s
  have hcc : ∀ s, c (c s) = s := fun s => by
    ext x
    simp [c]
  have hP : ∀ s, P s ↔ ¬ P (c s) := hσ.2
  have e1 : {s // P s} ≃ Ψ := (Equiv.ofInjective σ hσ.1).symm
  have e2 : {s // ¬ P s} ≃ {s // P s} :=
    { toFun := fun s => ⟨c s.1, by
        by_contra hn
        exact s.2 ((hP s.1).2 hn)⟩
      invFun := fun s => ⟨c s.1, (hP s.1).1 s.2⟩
      left_inv := fun s => Subtype.ext (hcc s.1)
      right_inv := fun s => Subtype.ext (hcc s.1) }
  have := Fintype.card_congr (Equiv.sumCompl P)
  rw [Fintype.card_sum, Fintype.card_congr e2, Fintype.card_congr e1, hc] at this
  omega

theorem one_le_rd : 1 ≤ hostRd E := by
  unfold hostRd
  refine Real.one_le_rpow ?_ (by positivity)
  have h : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
  rw [← Int.cast_abs]
  exact_mod_cast h

end Card

section Dens

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem measurable_ballDens (q : Ψ × Fin j × Fin j' ≃ Fin n) : Measurable (ballDens q) := by
  have hZ : ∀ τ, Continuous fun t : Fin n → ℂ => ballMat q t τ := fun τ =>
    continuous_matrix fun a b => continuous_apply _
  have hdet : ∀ τ, Measurable fun t : Fin n → ℂ =>
      Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re := fun τ =>
    Real.measurable_log.comp (Complex.continuous_re.comp
      (continuous_const.sub ((hZ τ).matrix_conjTranspose.matrix_mul (hZ τ))).matrix_det).measurable
  have hpot : Measurable (ballPot q) := by
    unfold ballPot
    exact (Finset.measurable_sum _ fun τ _ => hdet τ).neg
  unfold ballDens
  exact Real.measurable_exp.comp (hpot.const_mul _)

theorem ballDens_pos (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : 0 < ballDens q t := Real.exp_pos _

end Dens

end GlobalTheory.CompanionTheory.Ar.Cusp.BallMean

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open BallMean

theorem fund_set_mean_cuspW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)), F.IsArith Γ → F.IsFundSet Γ FF → 1 ≤ j' → 3 * j' + 1 ≤ j + j' → IntegrableOn (ballDens F.q) FF ∧ 0 < ∫ t in FF, ballDens F.q t ∧ IntegrableOn (fun t => (F.R t).cuspW F.σ * ballDens F.q t) FF ∧ ∫ t in FF, (F.R t).cuspW F.σ * ballDens F.q t ≤ Fintype.card Ψ * j' * (6 + Real.log (2 * Fintype.card Ψ * hostRd E) + Real.log (2 * Fintype.card Ψ * j' * hostRd E)) * ∫ t in FF, ballDens F.q t := by
  classical
  intro E _ _ _ Ψ _ j j' n g Λ _ _ H F Γ FF hA hFS hj' hN
  obtain ⟨Δ⟩ := GlobalTheory.T.exists_group_dictionary E Ψ j j' n g Λ H F
  have hcard := finrank_eq_two_mul F.cm
  have hrd : 1 ≤ hostRd E := one_le_rd
  have hf : 1 ≤ Fintype.card Ψ := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hfR : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast hf
  have hjR : (1 : ℝ) ≤ j' := by exact_mod_cast hj'
  set vr : ℝ := 2 * Fintype.card Ψ * hostRd E with hvrdef
  have hvr : 1 ≤ vr := by nlinarith
  have hvr0 : 0 < vr := by linarith
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.cm_field_small_integral_basis E
  have ha2' : ∀ i (s : E →+* ℂ), ‖s (a i)‖ ≤ vr := fun i s => by
    have := ha2 i s
    rw [hcard] at this
    rw [hvrdef]
    simpa using this
  let μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j')))) := Measure.haar
  obtain ⟨FD, hFD, h0, hT, hmean⟩ := GlobalTheory.T.first_minimum_integral_bound E Ψ j j' n g Λ F Δ μ vr hj' hN hvr0 ⟨a, ha1, ha2'⟩
  obtain ⟨C, hC0, hCT, hC⟩ := GlobalTheory.T.fundamental_set_to_fundamental_domain E Ψ j j' n g Λ F Δ μ Γ FF FD hA hFS hFD
  obtain ⟨hcont, hUm, hopen, hinv⟩ := GlobalTheory.T.first_minimum_continuous_cusp_weight_measurable E Ψ j j' n g Λ F hj'
  have hu1 : ∀ t ∈ ballDom F.q, _ := fun t ht =>
    GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ (F.R t) F.σ j' F.cm (fun τ => (F.sig t ht τ).1) hj'
  obtain ⟨hFFm, hFFsub, -, -⟩ := hFS
  set B := ballDom F.q with hB
  have hBm : MeasurableSet B := hopen.measurableSet
  set lam : (Fin n → ℂ) → ℝ := B.piecewise (fun t => (F.R t).lam1) 1 with hlam
  set U : (Fin n → ℂ) → ℝ := B.indicator fun t => (F.R t).cuspW F.σ with hU
  have hlamB : ∀ t ∈ B, lam t = (F.R t).lam1 := fun t ht => Set.piecewise_eq_of_mem _ _ _ ht
  have hUB : ∀ t ∈ B, U t = (F.R t).cuspW F.σ := fun t ht => Set.indicator_of_mem ht _
  have hlamm : Measurable lam := hcont.measurable_piecewise continuousOn_const hBm
  have hlampos : ∀ z, 0 < lam z := fun z => by
    by_cases hz : z ∈ B
    · rw [hlamB z hz]
      exact (hu1 z hz).1
    · have h1 : lam z = 1 := Set.piecewise_eq_of_notMem _ _ _ hz
      rw [h1]
      exact one_pos
  have hUnn : ∀ z, 0 ≤ U z := fun z => by
    by_cases hz : z ∈ B
    · rw [hUB z hz]
      exact (hu1 z hz).2.2.2.1
    · simp [hU, Set.indicator_of_notMem hz]
  have hUle : ∀ z, U z ≤ Fintype.card Ψ * j' * (2 * max 0 (Real.log (1 / lam z)) +
      Real.log (2 * Fintype.card Ψ * j' * hostRd E)) := fun z => by
    by_cases hz : z ∈ B
    · rw [hUB z hz, hlamB z hz]
      exact (hu1 z hz).2.2.2.2
    · have h1 : U z = 0 := by simp [hU, Set.indicator_of_notMem hz]
      rw [h1]
      have hl : 0 ≤ Real.log (2 * Fintype.card Ψ * j' * hostRd E) := by
        refine Real.log_nonneg ?_
        have : (1 : ℝ) ≤ (Fintype.card Ψ : ℝ) * j' := by nlinarith
        nlinarith
      have hm : (0 : ℝ) ≤ max 0 (Real.log (1 / lam z)) := le_max_left _ _
      positivity

  have hvol : ∫⁻ t in FF, ENNReal.ofReal (ballDens F.q t) = C * μ FD := by
    have := hC (fun _ => 1) measurable_const (fun _ _ _ _ _ => rfl)
    simpa using this
  have hV0 : ∫⁻ t in FF, ENNReal.ofReal (ballDens F.q t) ≠ 0 := by
    rw [hvol]
    exact mul_ne_zero hC0 h0
  have hVT : ∫⁻ t in FF, ENNReal.ofReal (ballDens F.q t) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.mul_ne_top hCT hT

  set r : ℝ := vr ^ (-(1 / 2 : ℝ)) with hr
  set Φ : (Fin n → ℂ) → ℝ≥0∞ := B.indicator fun t => ENNReal.ofReal (Real.log (r / lam t)) with hΦ
  have hΦm : Measurable Φ :=
    ((Real.measurable_log.comp (hlamm.const_div r)).ennreal_ofReal).indicator hBm
  have hΦB : ∀ t ∈ B, Φ t = ENNReal.ofReal (Real.log (r / lam t)) := fun t ht => Set.indicator_of_mem ht _
  have hΦinv : ∀ t ∈ B, ∀ t' ∈ B, F.Eqv (autGrp F.form) t t' → Φ t = Φ t' := fun t ht t' ht' he => by
    rw [hΦB t ht, hΦB t' ht', hlamB t ht, hlamB t' ht', (hinv t ht t' ht' he).1]
  have hπ : ∀ a, Δ.π a ∈ B := fun a => by
    rw [hB, ← Δ.π_range]
    exact Set.mem_range_self a
  have hmean' : ∫⁻ t in FF, ENNReal.ofReal (Real.log (r / lam t)) * ENNReal.ofReal (ballDens F.q t) ≤
      3 * ∫⁻ t in FF, ENNReal.ofReal (ballDens F.q t) := by
    have e1 : ∫⁻ t in FF, ENNReal.ofReal (Real.log (r / lam t)) * ENNReal.ofReal (ballDens F.q t) =
        ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) :=
      setLIntegral_congr_fun hFFm fun t ht => by rw [hΦB t (hFFsub ht)]
    have e2 : ∫⁻ a in FD, Φ (Δ.π a) ∂μ =
        ∫⁻ a in FD, ENNReal.ofReal (Real.log (vr ^ (-(1 / 2 : ℝ)) / (F.R (Δ.π a)).lam1)) ∂μ :=
      lintegral_congr fun a => by rw [hΦB _ (hπ a), hlamB _ (hπ a)]
    rw [e1, hC Φ hΦm hΦinv, hvol, e2]
    calc C * ∫⁻ a in FD, ENNReal.ofReal (Real.log (vr ^ (-(1 / 2 : ℝ)) / (F.R (Δ.π a)).lam1)) ∂μ
        ≤ C * (3 * μ FD) := by gcongr
      _ = 3 * (C * μ FD) := by rw [mul_left_comm]
  obtain ⟨i1, i2, i3, i4⟩ := weighted_mean volume FF (ballDens F.q) U lam (Fintype.card Ψ) j' vr (hostRd E)
    (measurable_ballDens F.q) (ballDens_pos F.q) hV0 hVT hUm hlamm hlampos hUnn hUle hf hj' hvr hrd hmean'
  have hUeq : ∀ t ∈ FF, U t * ballDens F.q t = (F.R t).cuspW F.σ * ballDens F.q t := fun t ht => by
    rw [hUB t (hFFsub ht)]
  refine ⟨i1, i2, i3.congr_fun hUeq hFFm, ?_⟩
  rw [← setIntegral_congr_fun hFFm hUeq]
  exact i4

end GlobalTheory.CompanionTheory.Ar.Cusp
