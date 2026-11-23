import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebrasMaxCompactAndLeviInterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLeviStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNilpotentAlgebraIsotropicFlagUnipotentRadiStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptoticStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeUnitaryMaximalCompactEqProdStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeMaximalCompactInterIsotropicFlagLeviStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLieAlgebrasRelativePositionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaGaugeDefiniteAndUnitBodyVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagDimensionCountStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedIwasawaIntegralSmallBallAsymptoticsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SlabMeasureSqueezeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLintegralUnfoldCompactLeviStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightInvariantEqSmulLeftInvariantProbabilityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueezeStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.IwConst

open Filter Topology

theorem triple_mono {G : Type} [MeasurableSpace G] {N M K : Set G} {μN μM μK : Measure G} (hN : μN Nᶜ = 0)
    (hM : μM Mᶜ = 0) (hK : μK Kᶜ = 0) (δ : G → ENNReal) {F F' : G → G → G → ENNReal}
    (h : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, F u m k ≤ F' u m k) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k ∂μK ∂μM ∂μN ≤ ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F' u m k ∂μK ∂μM ∂μN := by
  refine lintegral_mono_ae ?_
  filter_upwards [show N ∈ ae μN from mem_ae_iff.mpr hN] with u hu
  refine lintegral_mono_ae ?_
  filter_upwards [show M ∈ ae μM from mem_ae_iff.mpr hM] with m hm
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine lintegral_mono_ae ?_
  filter_upwards [show K ∈ ae μK from mem_ae_iff.mpr hK] with k hk
  exact h u hu m hm k hk

theorem triple_const {G : Type} [MeasurableSpace G] (μN μM μK : Measure G) (δ : G → ENNReal)
    (F : G → G → G → ENNReal) {V β : ENNReal} (hV : V ≠ ⊤) (hβ : β ≠ ⊤) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k * β ∂(V • μK) ∂μM ∂μN =
      V * β * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k ∂μK ∂μM ∂μN := by
  have hVβ : V * β ≠ ⊤ := ENNReal.mul_ne_top hV hβ
  simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_mul_const' _ _ hβ]
  have key : ∀ u m, δ m * (V * ((∫⁻ k, F u m k ∂μK) * β)) = V * β * (δ m * ∫⁻ k, F u m k ∂μK) := by
    intro u m; ring
  simp_rw [key, lintegral_const_mul' _ _ hVβ]

theorem ballVol_ne_zero (d : ℕ) : ballVol d ≠ 0 := by
  unfold ballVol
  exact (Metric.measure_ball_pos _ _ one_pos).ne'

theorem ballVol_ne_top (d : ℕ) : ballVol d ≠ ⊤ := by
  unfold ballVol
  exact measure_ball_lt_top.ne

theorem volU_pos' (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  refine mul_pos (Finset.prod_pos fun l _ => ?_) (by positivity)
  positivity

theorem tendsto_mul_balls {f g : ℝ → ENNReal} {d e : ℕ} {V : ENNReal} (hV : V ≠ ⊤)
    (hf : Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (𝓝[>] 0) (𝓝 (ballVol d)))
    (hg : Tendsto (fun r : ℝ => g r / ENNReal.ofReal (r ^ e)) (𝓝[>] 0) (𝓝 (ballVol e))) :
    Tendsto (fun r : ℝ => V * f r * g r / ENNReal.ofReal (r ^ (d + e))) (𝓝[>] 0)
      (𝓝 (V * (ballVol d * ballVol e))) := by
  have hlim : Tendsto (fun r : ℝ => V * ((f r / ENNReal.ofReal (r ^ d)) * (g r / ENNReal.ofReal (r ^ e))))
      (𝓝[>] 0) (𝓝 (V * (ballVol d * ballVol e))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul hf (Or.inr (ballVol_ne_top e)) hg (Or.inr (ballVol_ne_top d))) (Or.inr hV)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) ≤ r := le_of_lt hr
  rw [pow_add, ENNReal.ofReal_mul (pow_nonneg hr' _), div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
  ring

private theorem hs_conjTranspose_mul_mul_of_unitary {n : ℕ} (U X : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    Formalism.REAL.hs (Uᴴ * X * U) = Formalism.REAL.hs X := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have key : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ((Formalism.REAL.hs Y : ℝ) : ℂ) = (Y * Yᴴ).trace := by
    intro Y
    simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have h1 : ((Formalism.REAL.hs (Uᴴ * X * U) : ℝ) : ℂ) = ((Formalism.REAL.hs X : ℝ) : ℂ) := by
    rw [key, key, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc, hU', Matrix.mul_one]
  exact_mod_cast h1

private theorem map_mul_right_eq_of_isGaugeSub {n : ℕ} {ε : Fin n → Bool} (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    {d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hAE : ∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E))
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub {g | uMat g - 1 ∈ A} d μ)
    (l : Formalism.REAL.UJ ε) (hl : uMat l - 1 ∈ A) (hu : (uMat l)ᴴ * uMat l = 1) :
    μ.map (fun g => g * l) = μ := by
  have huniq := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hAE μ hμ).2.2.1
  have hcut : IsCut ε {g | uMat g - 1 ∈ A} E := ⟨A, hA, hE, hAE, rfl⟩
  obtain ⟨H, hH, -⟩ := hcut.subgroup
  have hlH : l ∈ H := by rw [← SetLike.mem_coe, hH]; exact hl
  have hlinv : l⁻¹ ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ A} := by
    rw [← hH]; exact H.inv_mem hlH
  have hinvU : uMat l⁻¹ = (uMat l)ᴴ := by
    have h1 : uMat l⁻¹ * uMat l = 1 := by simp [uMat]
    calc uMat l⁻¹ = uMat l⁻¹ * (uMat l * (uMat l)ᴴ) := by rw [mul_eq_one_comm.mp hu, Matrix.mul_one]
      _ = (uMat l)ᴴ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  apply huniq
  obtain ⟨h0, hinv, hlim⟩ := hμ
  have he : (fun g : Formalism.REAL.UJ ε => g * l) = ⇑(MeasurableEquiv.mulRight l) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [he, MeasurableEquiv.map_apply, ← hH]
    have hpre : ⇑(MeasurableEquiv.mulRight l) ⁻¹' (↑H)ᶜ = (↑H : Set (Formalism.REAL.UJ ε))ᶜ := by
      ext g
      simp [H.mul_mem_cancel_right hlH]
    rw [hpre, hH]
    exact h0
  · intro s hs
    rw [Measure.map_map (measurable_const_mul s) (measurable_mul_const l),
      show ((fun g => s * g) ∘ fun g => g * l) = (fun g => g * l) ∘ (fun g => s * g) by
        funext g; simp [mul_assoc],
      ← Measure.map_map (measurable_mul_const l) (measurable_const_mul s), hinv s hs]
  · refine hlim.congr (fun r => ?_)
    congr 1
    rw [he, MeasurableEquiv.map_apply]
    conv_rhs => rw [← hinv l⁻¹ hlinv]
    have he2 : (fun g : Formalism.REAL.UJ ε => l⁻¹ * g) = ⇑(MeasurableEquiv.mulLeft l⁻¹) := rfl
    rw [he2, MeasurableEquiv.map_apply]
    congr 1
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq, MeasurableEquiv.coe_mulRight, MeasurableEquiv.coe_mulLeft]
    have hg : uMat (l⁻¹ * g * l) - 1 = (uMat l)ᴴ * (uMat g - 1) * uMat l := by
      rw [show uMat (l⁻¹ * g * l) = uMat l⁻¹ * uMat g * uMat l by simp [uMat], hinvU]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu]
    rw [hg, hs_conjTranspose_mul_mul_of_unitary _ _ hu]

private theorem lintegral_lintegral_mul_const {G : Type} [MeasurableSpace G] (μN μM μK : Measure G) (δ : G → ENNReal)
    (F : G → G → G → ENNReal) {β : ENNReal} (hβ : β ≠ ⊤) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k * β ∂μK ∂μM ∂μN = β * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k ∂μK ∂μM ∂μN := by
  have h := triple_const μN μM μK δ F (V := 1) ENNReal.one_ne_top hβ
  rw [one_smul, one_mul] at h
  exact h

private theorem lintegral_indicator_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G)
    {s : Set G} (hs : MeasurableSet s) (k : G) :
    ∫⁻ l, s.indicator 1 (l * k) ∂ν = ν {l | l * k ∈ s} := by
  have h := lintegral_indicator_one (μ := ν) (measurable_mul_const k hs)
  refine Eq.trans ?_ h
  congr 1

theorem iwasawa_constant : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∀ (c : ℝ) (κ : ENNReal), IsGauge ε c → (∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN) → ENNReal.ofReal c * κ = ENNReal.ofReal (cIw p q j) := by
  intro n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv c κ hc hform
  obtain ⟨hpq, hn2, hdK⟩ := GlobalTheory.T.isotropicFlag_dimension_count n ε a j W hW p q hp hq
  obtain ⟨AN, EN, hAN, hEN, hAEN, hNset⟩ := GlobalTheory.T.exists_nilpotentAlgebra_isotropicFlagUnipotentRadical n ε a j W hW
  obtain ⟨AM, EM, hAM, hEM, hAEM, hMset⟩ := GlobalTheory.T.exists_algebra_isotropicFlagSelfAdjointLevi n ε a j W hW
  obtain ⟨⟨AK, EK, hAK, hEK, hAEK, hKset⟩, ⟨AL, EL, hAL, hEL, hAEL, hLset⟩⟩ :=
    GlobalTheory.T.exists_algebras_maxCompact_and_levi_inter n ε a j W hW p q hp hq
  have cN : IsCut ε (flagN ε W) EN := ⟨AN, hAN, hEN, hAEN, hNset⟩
  have cM : IsCut ε (flagM ε W) EM := ⟨AM, hAM, hEM, hAEM, hMset⟩
  have cK : IsCut ε (maxK ε) EK := ⟨AK, hAK, hEK, hAEK, hKset⟩
  have cL : IsCut ε (maxK ε ∩ flagM ε W) EL := ⟨AL, hAL, hEL, hAEL, hLset⟩
  have hrel := GlobalTheory.T.iwasawa_lieAlgebras_relative_position n ε a j W hW _ _ _ _ EN EM EK EL cN cM cK cL
  obtain ⟨hnd, hvol⟩ := GlobalTheory.T.iwasawaGauge_definite_and_unitBody_volume n _ _ _ _ EN EM EK EL cN.isON cM.isON cK.isON cL.isON hrel hdK

  have hN' : IsGaugeSub {g | uMat g - 1 ∈ AN} (dimN n j) μN := by rw [← hNset]; exact hN
  have hM' : IsGaugeSub {g | uMat g - 1 ∈ AM} ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM := by
    rw [← hMset]; exact hM
  have : SigmaFinite μN := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε AN _ EN hAN hEN hAEN μN hN').1
  have : SigmaFinite μM := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε AM _ EM hAM hEM hAEM μM hM').1
  obtain ⟨νL, hνσ, hνL⟩ := GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε AL _ EL hAL hEL hAEL
  have := hνσ
  have hνL' : IsGaugeSub (maxK ε ∩ flagM ε W) ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) νL := by
    rw [hLset]; exact hνL
  have : IsFiniteMeasureOnCompacts νL := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε AL _ EL hAL hEL hAEL νL hνL).2.1
  obtain ⟨μ0, hμ0σ, hμ0⟩ := GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε AK _ EK hAK hEK hAEK
  have := hμ0σ
  have hμ0' : IsGaugeSub (maxK ε) (p ^ 2 + q ^ 2) μ0 := by rw [hKset]; exact hμ0
  have hVK := GlobalTheory.T.volume_unitaryMaximalCompact_eq_prod n ε p q hp hq μ0 hμ0'
  have hVL := GlobalTheory.T.volume_maximalCompact_inter_isotropicFlagLevi n ε p q hp hq a j W hW νL hνL'

  have rK : ∀ l ∈ maxK ε, μ0.map (fun g => g * l) = μ0 := fun l hl =>
    map_mul_right_eq_of_isGaugeSub AK EK hAK hEK hAEK μ0 hμ0 l (by
      have h : l ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ AK} := by rw [← hKset]; exact hl
      exact h) hl
  have rM : ∀ l ∈ maxK ε ∩ flagM ε W, μM.map (fun g => g * l) = μM := fun l hl =>
    map_mul_right_eq_of_isGaugeSub AM EM hAM hEM hAEM μM hM' l (by
      have h : l ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ AM} := by rw [← hMset]; exact hl.2
      exact h) hl.1
  have rL : ∀ l ∈ maxK ε ∩ flagM ε W, νL.map (fun g => g * l) = νL := fun l hl =>
    map_mul_right_eq_of_isGaugeSub AL EL hAL hEL hAEL νL hνL l (by
      have h : l ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ AL} := by rw [← hLset]; exact hl
      exact h) hl.1
  have : IsProbabilityMeasure μK := ⟨hK1⟩
  have hμ0eq := GlobalTheory.T.right_invariant_eq_smul_left_invariant_probability (Formalism.REAL.UJ ε) (maxK ε) μK μ0 hK0 hμ0'.1 hK1 hKinv rK
  rw [hVK] at hμ0eq

  have hvpos : ∀ i, 0 < volU i := volU_pos'
  have hVtop : ENNReal.ofReal (volU p * volU q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hδ := GlobalTheory.T.leviFactorInverseModulus_properties n ε a j W
  have hΓtop : volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ballVol_ne_top _)) (ballVol_ne_top _)
  obtain ⟨ρ₀, hρ₀, hlimS⟩ := GlobalTheory.T.localisedIwasawaIntegral_smallBall_asymptotics n ε a j W hW _ _ _ _ EN EM EK EL cN cM cK cL.isON hnd hΓtop
    μN μM μ0 hN hM hμ0'
  have hρ : 0 < min ρ₀ (1 / 8) := lt_min hρ₀ (by norm_num)
  have hS := hlimS (min ρ₀ (1 / 8)) hρ (min_le_left _ _)
  set ρ := min ρ₀ (1 / 8) with hρdef

  obtain ⟨Fp, hFp⟩ : ∃ F : ℝ → ENNReal, F = fun r =>
      ∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) ∂μ0 ∂μM ∂μN := ⟨_, rfl⟩
  obtain ⟨Sp, hSp⟩ : ∃ F : ℝ → ENNReal, F = fun r =>
      ∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) * (slab ε EL ρ r).indicator 1 k
        ∂μ0 ∂μM ∂μN := ⟨_, rfl⟩
  have hBtop : ∀ s, νL (hsBall ε s) ≠ ⊤ := fun s => ((isCompact_hsBall ε s).measure_lt_top).ne

  have hFmono : ∀ s r, s ≤ r → Fp s ≤ Fp r := by
    intro s r hsr
    simp only [hFp]
    refine triple_mono hN.1 hM.1 hμ0'.1 _ (fun u _ m _ k _ => ?_)
    refine Set.indicator_le_indicator_of_subset (fun g hg => ?_) (fun _ => by positivity) _
    exact (le_trans hg hsr : nrm (uMat g - 1) ≤ r)

  have hsand : ∀ η : ℝ, 0 < η → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      νL (hsBall ε (r / (1 + η))) * Fp r ≤ νL Set.univ * Sp r ∧
        νL Set.univ * Sp r ≤ νL (hsBall ε ((1 + η) * r)) * Fp r := by
    intro η hη
    filter_upwards [GlobalTheory.T.slab_measure_squeeze' n ε a j W hW _ EL cL hrel.2.2.2.2.2.1 νL hνL'.1 rL ρ η hρ
      (min_le_right _ _) hη] with r hr
    have hswap := GlobalTheory.T.iwasawa_lintegral_unfold_compact_levi (Formalism.REAL.UJ ε) (flagM ε W) (maxK ε ∩ flagM ε W) μN μM μ0 νL (dlt j W)
      ((hsBall ε r).indicator 1) ((slab ε EL ρ r).indicator 1) hδ.1
      (measurable_one.indicator (measurableSet_hsBall ε r)) (measurable_one.indicator (measurableSet_slab ε EL ρ r))
      hM.1 hνL'.1 rM (fun l hl => hμ0'.2.1 l hl.1) hδ.2.1
    simp only [hSp, hFp]
    rw [hswap]
    constructor
    · rw [← lintegral_lintegral_mul_const _ _ _ _ _ (hBtop _)]
      refine triple_mono hN.1 hM.1 hμ0'.1 _ (fun u hu m hm k hk => ?_)
      by_cases hmem : u * m * k ∈ hsBall ε r
      · rw [Set.indicator_of_mem hmem, lintegral_indicator_mul_right νL (measurableSet_slab ε EL ρ r) k]
        simp only [Pi.one_apply, one_mul]
        exact (hr u hu m hm k hk hmem).1
      · simp [hmem]
    · rw [← lintegral_lintegral_mul_const _ _ _ _ _ (hBtop _)]
      refine triple_mono hN.1 hM.1 hμ0'.1 _ (fun u hu m hm k hk => ?_)
      by_cases hmem : u * m * k ∈ hsBall ε r
      · rw [Set.indicator_of_mem hmem, lintegral_indicator_mul_right νL (measurableSet_slab ε EL ρ r) k]
        simp only [Pi.one_apply, one_mul]
        exact (hr u hu m hm k hk hmem).2
      · simp [hmem]

  have hf : Tendsto (fun r : ℝ => ENNReal.ofReal c * Formalism.REAL.muG ε (hsBall ε r) / ENNReal.ofReal (r ^ (n ^ 2)))
      (𝓝[>] 0) (𝓝 (ballVol (n ^ 2))) := by
    have h3 := ((GlobalTheory.T.riemannianHaarGauge_whole_group n ε).1 c hc).2.2.2
    refine h3.congr (fun r => ?_)
    rw [Measure.smul_apply, smul_eq_mul]
    rfl
  have hg : Tendsto (fun r : ℝ => νL (hsBall ε r) /
      ENNReal.ofReal (r ^ ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2))) (𝓝[>] 0)
      (𝓝 (ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2))) := hνL'.2.2
  have hFK : ∀ r, Fp r = ENNReal.ofReal (volU p * volU q) *
      ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) *
        ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) ∂μK ∂μM ∂μN := by
    intro r
    have h := triple_const μN μM μK (dlt j W) (fun u m k => (hsBall ε r).indicator 1 (u * m * k)) hVtop
      ENNReal.one_ne_top
    simp only [mul_one] at h
    simp only [hFp]
    rw [hμ0eq, h]
    rfl
  have hmuG : ∀ r, Formalism.REAL.muG ε (hsBall ε r) = κ *
      ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) *
        ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) ∂μK ∂μM ∂μN := by
    intro r
    rw [← hform _ (measurable_one.indicator (measurableSet_hsBall ε r)), lintegral_indicator_one
      (measurableSet_hsBall ε r)]
  have hb : Tendsto (fun r : ℝ => ENNReal.ofReal c * κ * (Fp r * νL (hsBall ε r)) /
      ENNReal.ofReal (r ^ (n ^ 2 + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (volU p * volU q) * (ballVol (n ^ 2) *
        ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)))) := by
    refine (tendsto_mul_balls hVtop hf hg).congr (fun r => ?_)
    rw [hFK, hmuG]
    congr 1
    ring
  have hvtop : ENNReal.ofReal (volU p * volU q) * (ballVol (n ^ 2) *
      ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top hVtop (ENNReal.mul_ne_top (ballVol_ne_top _) (ballVol_ne_top _))
  have hF := GlobalTheory.T.tendsto_small_ball_density_of_squeeze (fun r => ENNReal.ofReal c * κ * (νL Set.univ * Sp r)) _ _ hvtop (fun η hη => by
    refine ⟨fun r => ENNReal.ofReal c * κ * (Fp r * νL (hsBall ε r)), hb, ?_⟩
    have h1η : (1 : ENNReal) ≤ ENNReal.ofReal (1 + η) := ENNReal.one_le_ofReal.mpr (by linarith)
    filter_upwards [hsand η hη, self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    constructor
    · refine le_trans ?_ (le_mul_of_one_le_left (by positivity) h1η)
      show ENNReal.ofReal c * κ * (Fp (r / (1 + η)) * νL (hsBall ε (r / (1 + η)))) ≤
        ENNReal.ofReal c * κ * (νL Set.univ * Sp r)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc Fp (r / (1 + η)) * νL (hsBall ε (r / (1 + η))) ≤ Fp r * νL (hsBall ε (r / (1 + η))) :=
            mul_le_mul_of_nonneg_right (hFmono _ _ (div_le_self hr0'.le (by linarith))) (by positivity)
        _ = νL (hsBall ε (r / (1 + η))) * Fp r := mul_comm _ _
        _ ≤ νL Set.univ * Sp r := hr.1
    · refine le_trans ?_ (le_mul_of_one_le_left (by positivity) h1η)
      show ENNReal.ofReal c * κ * (νL Set.univ * Sp r) ≤
        ENNReal.ofReal c * κ * (Fp ((1 + η) * r) * νL (hsBall ε ((1 + η) * r)))
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc νL Set.univ * Sp r ≤ νL (hsBall ε ((1 + η) * r)) * Fp r := hr.2
        _ ≤ νL (hsBall ε ((1 + η) * r)) * Fp ((1 + η) * r) :=
            mul_le_mul_of_nonneg_left (hFmono _ _ (by nlinarith)) (by positivity)
        _ = Fp ((1 + η) * r) * νL (hsBall ε ((1 + η) * r)) := mul_comm _ _)

  have hexp : dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2 + (p ^ 2 + q ^ 2)) =
      n ^ 2 + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
    rw [hdK, hn2]; ring
  have hΓ0 : volume {v | gau EN EM EK EL v ≤ 1} ≠ 0 := by
    rw [hvol]
    refine mul_ne_zero (mul_ne_zero ?_ (ballVol_ne_zero _)) (ballVol_ne_zero _)
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hF2 : Tendsto (fun r => ENNReal.ofReal c * κ * (νL Set.univ * Sp r) /
      ENNReal.ofReal (r ^ (n ^ 2 + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal c * κ * νL Set.univ * volume {v | gau EN EM EK EL v ≤ 1})) := by
    rw [← hexp]
    refine (ENNReal.Tendsto.const_mul hS (Or.inl hΓ0)).congr (fun r => ?_)
    simp only [hSp]
    rw [mul_div_assoc, mul_div_assoc, mul_assoc]
  have heq := tendsto_nhds_unique hF2 hF

  rw [hvol, hVL, ← hn2] at heq
  have hB0 : ballVol (n ^ 2) * ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) ≠ 0 :=
    mul_ne_zero (ballVol_ne_zero _) (ballVol_ne_zero _)
  have hBt : ballVol (n ^ 2) * ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ballVol_ne_top _) (ballVol_ne_top _)
  have hAL : 0 < (∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) *
      volU (q - ∑ i, j i) :=
    mul_pos (mul_pos (Finset.prod_pos fun i _ => mul_pos (hvpos _) (by positivity)) (hvpos _)) (hvpos _)
  have hT : (0 : ℝ) < (2 : ℝ) ^ ((dimN n j : ℝ) / 2) := by positivity
  have heq2 : ENNReal.ofReal c * κ * (ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2))) =
      ENNReal.ofReal (volU p * volU q) := by
    refine (ENNReal.mul_left_inj hB0 hBt).mp ?_
    rw [← heq]
    ring
  have hc0 : 0 ≤ cIw p q j := by
    unfold cIw
    exact (div_pos (mul_pos (by positivity) (mul_pos (hvpos p) (hvpos q))) hAL).le
  have hcIw : ENNReal.ofReal (cIw p q j) * (ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2))) =
      ENNReal.ofReal (volU p * volU q) := by
    rw [← ENNReal.ofReal_mul hAL.le, ← ENNReal.ofReal_mul hc0]
    congr 1
    have h2 : (2 : ℝ) ^ (-((dimN n j : ℝ) / 2)) * (2 : ℝ) ^ ((dimN n j : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    unfold cIw
    rw [hpq]
    rw [show ∀ x y z w : ℝ, x * y / z * (z * w) = x * w * y * (z / z) by intros; ring, div_self hAL.ne', h2]
    ring
  have hne0 : ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2)) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hAL).ne' (ENNReal.ofReal_pos.mpr hT).ne'
  have hnet : ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.mul_left_inj hne0 hnet).mp (heq2.trans hcIw.symm)

end GlobalTheory.IwConst
