import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallBallAsymptoticsPiWeightedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompleteIsotropicFrameSignatureEigenvectorsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockDiagUnitaryProductHomStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaxCompactInterLeviIffFrameStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.LeviCompact

theorem continuous_hs_uMat {n : ℕ} (ε : Fin n → Bool) :
    Continuous fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1) := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  unfold Formalism.REAL.hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
  exact ((continuous_apply k).comp ((continuous_apply i).comp (hc.sub continuous_const))).norm.pow 2

theorem compactSpace_allPos (N : ℕ) : CompactSpace (Formalism.REAL.UJ (allPos N)) := by
  obtain ⟨hE, hR⟩ := Formalism.REAL.uJEmb N (allPos N)
  have hJ : Formalism.REAL.Jm (allPos N) = 1 := by
    simp [Formalism.REAL.Jm, allPos, Matrix.diagonal_one]
  rw [← isCompact_univ_iff, hE.isCompact_iff, Set.image_univ, hR]
  have hcl : IsClosed {g : Matrix (Fin N) (Fin N) ℂ | Formalism.REAL.inUJ (allPos N) g} := by
    simp only [Formalism.REAL.inUJ]
    exact isClosed_eq (by fun_prop) continuous_const
  have hK : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset hcl ?_
  intro g hg i _ k _
  simp only [Formalism.REAL.inUJ, hJ, Matrix.mul_one] at hg
  have h := congrFun (congrFun hg k) k
  simp only [Matrix.one_apply_eq] at h
  have h2 : ∑ r, (Complex.normSq (g r k) : ℂ) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun r _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have h3 : ∑ r, Complex.normSq (g r k) = 1 := by exact_mod_cast h2
  have h4 : Complex.normSq (g i k) ≤ 1 :=
    h3 ▸ Finset.single_le_sum (fun r _ => Complex.normSq_nonneg (g r k)) (Finset.mem_univ i)
  rw [Metric.mem_closedBall, dist_zero_right]
  have h5 : ‖g i k‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact h4
  nlinarith [norm_nonneg (g i k)]

theorem exists_eq_mul_preimage {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (ν : Measure G) [ν.IsHaarMeasure]
    (Φ : G →* H) (hc : Continuous Φ) (hi : Function.Injective Φ) (μ : Measure H) (h0 : μ (Set.range Φ)ᶜ = 0)
    (hinv : ∀ s ∈ Set.range Φ, μ.map (fun g => s * g) = μ) {U : Set H} (hU : IsOpen U) (h1 : (1 : H) ∈ U)
    (hfin : μ U ≠ ⊤) : ∃ α : NNReal, ∀ A, μ A = α * ν (Φ ⁻¹' A) := by
  have hemb : Topology.IsClosedEmbedding Φ := hc.isClosedEmbedding hi
  have hme : MeasurableEmbedding Φ := hemb.measurableEmbedding
  set ν' : Measure G := μ.comap Φ with hν'
  have hae : ∀ᵐ x ∂μ, x ∈ Set.range Φ := by rw [ae_iff]; exact h0
  have hres : μ.restrict (Set.range Φ) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hkey : ∀ B, μ B = ν' (Φ ⁻¹' B) := by
    intro B
    rw [hν', ← hme.map_apply, hme.map_comap, hres]
  have hinvG : ν'.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs]
    have h1 : (fun x => g * x) ⁻¹' s = Φ ⁻¹' ((fun y => Φ g * y) ⁻¹' (Φ '' s)) := by
      ext x
      simp only [Set.mem_preimage, ← map_mul, hi.mem_set_image]
    have h2 : s = Φ ⁻¹' (Φ '' s) := (Set.preimage_image_eq s hi).symm
    rw [h1, ← hkey, ← Measure.map_apply (measurable_const_mul (Φ g)) (hme.measurableSet_image.2 hs),
      hinv _ ⟨g, rfl⟩, hkey, ← h2]
  have hV : IsOpen (Φ ⁻¹' U) := hU.preimage hc
  have hVfin : ν' (Φ ⁻¹' U) ≠ ⊤ := by rw [← hkey]; exact hfin
  have hfinU : ν' Set.univ < ⊤ := by
    refine isCompact_univ.measure_lt_top_of_nhdsWithin fun x _ => ⟨(fun y => x⁻¹ * y) ⁻¹' (Φ ⁻¹' U), ?_, ?_⟩
    · rw [nhdsWithin_univ]
      exact (hV.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [h1])
    · rw [measure_preimage_mul]; exact hVfin.lt_top
  have : IsFiniteMeasure ν' := ⟨hfinU⟩
  have heq := Measure.isMulLeftInvariant_eq_smul ν' ν
  refine ⟨Measure.haarScalarFactor ν' ν, fun A => ?_⟩
  have h3 := congrArg (fun m : Measure G => m (Φ ⁻¹' A)) heq
  rw [hkey A, h3, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

theorem volume_range : ∀ (n : ℕ) (ε : Fin n → Bool) (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ι → ℝ) (Φ : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Formalism.REAL.UJ ε), (∀ i, 0 < w i) → Continuous Φ → Function.Injective Φ → (∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ i, w i * Formalism.REAL.hs (uMat (g i) - 1)) → ∀ μ, IsGaugeSub (Set.range Φ) (∑ i, m i ^ 2) μ → μ Set.univ = ENNReal.ofReal (∏ i, volU (m i) * w i ^ (((m i : ℝ)) ^ 2 / 2)) := by
  intro n ε ι _ m w Φ hw hc hi hhs μ hμ
  obtain ⟨h0, hinv, hlim⟩ := hμ
  have hcpt : ∀ i, CompactSpace (Formalism.REAL.UJ (allPos (m i))) := fun i => compactSpace_allPos _
  choose c hcpos hcg _ using fun i => GlobalTheory.GaugeConst.gauge_exists_pos_unique (m i) (allPos (m i))
  set νi : ∀ i, Measure (Formalism.REAL.UJ (allPos (m i))) :=
    fun i => ENNReal.ofReal (c i) • Formalism.REAL.muG (allPos (m i)) with hνi
  have hfin : ∀ i, IsFiniteMeasure (νi i) := fun i => ⟨by
    simp only [hνi, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  have hhaar : ∀ i, (νi i).IsHaarMeasure := fun i =>
    Measure.IsHaarMeasure.smul _ (by simpa using hcpos i) ENNReal.ofReal_ne_top
  set ν : Measure (∀ i, Formalism.REAL.UJ (allPos (m i))) := Measure.pi νi with hν
  set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, m i ^ 2))) 1) with hV
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  obtain ⟨r, hr0, hrfin⟩ : ∃ r : ℝ, 0 < r ∧ μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    have e1 := hlim.eventually (gt_mem_nhds (show V < V + 1 from ENNReal.lt_add_right hVtop one_ne_zero))
    have e2 : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < r := self_mem_nhdsWithin
    obtain ⟨r, h1, h2⟩ := (e1.and e2).exists
    refine ⟨r, h2, fun htop => ?_⟩
    rw [htop, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at h1
    exact absurd h1 (not_lt.2 le_top)
  set U := {g : Formalism.REAL.UJ ε | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < r} with hU
  have hUo : IsOpen U := isOpen_lt (Real.continuous_sqrt.comp (continuous_hs_uMat ε)) continuous_const
  have hu1 : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  have hU1 : (1 : Formalism.REAL.UJ ε) ∈ U := by simp [hU, Formalism.REAL.hs, hu1, hr0]
  have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top hrfin (measure_mono fun g (hg : g ∈ U) => by
    simp only [hU, Set.mem_setOf_eq] at hg ⊢; exact hg.le)
  obtain ⟨α, hα⟩ := exists_eq_mul_preimage ν Φ hc hi μ h0 hinv hUo hU1 hUfin
  have hfac : ∀ i, Filter.Tendsto (fun r : ℝ => νi i {x | Real.sqrt (Formalism.REAL.hs (uMat x - 1)) ≤ r} /
      ENNReal.ofReal (r ^ (m i ^ 2))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m i ^ 2))) 1))) := by
    intro i
    have hg := hcg i
    unfold GlobalTheory.Count.IsGauge at hg
    have h1 := ENNReal.tendsto_ofReal hg
    rw [ENNReal.ofReal_toReal measure_ball_lt_top.ne] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    simp only [hνi, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_div_of_pos (pow_pos hr _), ENNReal.ofReal_mul (hcpos i).le,
      ENNReal.ofReal_toReal (measure_lt_top _ _).ne]
  have hprod := GlobalTheory.T.smallBall_asymptotics_pi_weighted ι (fun i => Formalism.REAL.UJ (allPos (m i))) νi (fun i x => Formalism.REAL.hs (uMat x - 1))
    (fun i => m i ^ 2) w (fun i => (continuous_hs_uMat _).measurable)
    (fun i x => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hw hfac
  set K : ℝ := ∏ i, w i ^ (-(((m i ^ 2 : ℕ) : ℝ) / 2)) with hK
  have hpre : ∀ r, Φ ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
      {x | Real.sqrt (∑ i, w i * Formalism.REAL.hs (uMat (x i) - 1)) ≤ r} := by
    intro r; ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, hhs]
  have hlim2 : Filter.Tendsto (fun r : ℝ => (α : ENNReal) * (ν {x | Real.sqrt (∑ i, w i * Formalism.REAL.hs (uMat (x i) - 1)) ≤ r} /
      ENNReal.ofReal (r ^ (∑ i, m i ^ 2)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds V) := by
    refine hlim.congr' (Filter.Eventually.of_forall fun r => ?_)
    simp only
    rw [hα, hpre, mul_div_assoc]
  have hlim3 := ENNReal.Tendsto.const_mul hprod (Or.inr (ENNReal.coe_ne_top (r := α)))
  have heq : V = (α : ENNReal) * (ENNReal.ofReal K * V) := tendsto_nhds_unique hlim2 hlim3
  have h1 : (α : ENNReal) * ENNReal.ofReal K = 1 := by
    have e : V = ((α : ENNReal) * ENNReal.ofReal K) * V := by rw [mul_assoc]; exact heq
    calc _ = ((α : ENNReal) * ENNReal.ofReal K) * V / V := (ENNReal.mul_div_cancel_right hV0 hVtop).symm
      _ = V / V := by rw [← e]
      _ = 1 := ENNReal.div_self hV0 hVtop
  have hKpos : 0 < K := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hw i) _
  have hvol0 : ∀ i, 0 ≤ volU (m i) := fun i => by
    rw [← GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq (m i) (c i) (hcg i)]; exact mul_nonneg (hcpos i).le ENNReal.toReal_nonneg
  have hνu : ν Set.univ = ∏ i, ENNReal.ofReal (volU (m i)) := by
    rw [hν, Measure.pi_univ]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hνi, Measure.smul_apply, smul_eq_mul]
    rw [← GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq (m i) (c i) (hcg i), ENNReal.ofReal_mul (hcpos i).le,
      ENNReal.ofReal_toReal (measure_lt_top _ _).ne]
  rw [hα, Set.preimage_univ, hνu, ENNReal.eq_inv_of_mul_eq_one_left h1, ← ENNReal.ofReal_inv_of_pos hKpos,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => hvol0 i), ← ENNReal.ofReal_mul (inv_nonneg.2 hKpos.le)]
  congr 1
  rw [Finset.prod_mul_distrib, mul_comm, hK, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.rpow_neg (hw i).le, inv_inv]
  push_cast
  ring_nf

private theorem fintype_sum_matrix_mul_eq_sum_mul {n m : ℕ} {ι : Type} [Fintype ι] (A : ι → Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ) : (∑ i, A i) * B = ∑ i, A i * B := by
  ext r c
  simp only [Matrix.mul_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem exists_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∃ (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) ∧ (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  intro n ε p q hp hq a j W hW
  obtain ⟨h0, hmono, hrk, hiso⟩ := hW
  obtain ⟨T, hTT, hTo, hmem⟩ := GlobalTheory.T.exists_orthonormal_frame_of_flag_alt n a j W h0 hmono hrk
  have hcol : ∀ k (d : Fin (j k)), (fun r => T k r d) ∈ W (Fin.last a) := by
    intro k d
    rw [hmem]
    have hf : (univ.filter fun i : Fin a => i.val < (Fin.last a).val) = univ :=
      Finset.filter_true_of_mem fun i _ => i.isLt
    rw [hf]
    have hs : (∑ i, T i * (T i)ᴴ) * T k = T k := by
      rw [fintype_sum_matrix_mul_eq_sum_mul, Finset.sum_eq_single k]
      · rw [Matrix.mul_assoc, hTT, Matrix.mul_one]
      · intro i _ hik; rw [Matrix.mul_assoc, hTo i k hik, Matrix.mul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    have hy : (fun r => T k r d) = T k *ᵥ Pi.single d 1 := by
      ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hy, Matrix.mulVec_mulVec, hs]
  have hTJT : ∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0 := by
    intro i k
    ext c d
    have h := hiso _ (hcol i c) _ (hcol k d)
    rw [Matrix.zero_apply, ← h]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  obtain ⟨P, Q, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.complete_isotropicFrame_signature_eigenvectors n ε p q hp hq a j T hTT hTo hTJT
  exact ⟨T, P, Q, hTT, hTo, hTJT, h1, h2, h3, h4, h5, h6, h7, hmem⟩

private theorem levi_lemma {n a p' q' : ℕ} {j : Fin a → ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (K : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (U : Matrix (Fin p') (Fin p') ℂ) (V : Matrix (Fin q') (Fin q') ℂ)
    (hJJ : J * J = 1) (hJP : J * P = P) (hJQ : J * Q = -Q) (e1 : Pᴴ * J = Pᴴ) (e2 : Qᴴ * J = -Qᴴ)
    (hJH : Jᴴ = J) :
    J * (∑ i, T i * K i * (T i)ᴴ + (∑ i, J * T i * K i * (J * T i)ᴴ + (P * U * Pᴴ + Q * V * Qᴴ))) =
      (∑ i, T i * K i * (T i)ᴴ + (∑ i, J * T i * K i * (J * T i)ᴴ + (P * U * Pᴴ + Q * V * Qᴴ))) * J := by
  have a1 : ∀ {r : ℕ} (X : Matrix (Fin n) (Fin r) ℂ), J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have a2 : ∀ {r : ℕ} (X : Matrix (Fin p') (Fin r) ℂ), J * (P * X) = P * X := fun X => by
    rw [← Matrix.mul_assoc, hJP]
  have a3 : ∀ {r : ℕ} (X : Matrix (Fin q') (Fin r) ℂ), J * (Q * X) = -(Q * X) := fun X => by
    rw [← Matrix.mul_assoc, hJQ, Matrix.neg_mul]
  simp only [Matrix.conjTranspose_mul, hJH, Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul,
    Matrix.mul_assoc, a1, a2, a3, e1, e2, hJJ, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    Finset.sum_add_distrib]
  abel

set_option maxHeartbeats 1000000 in

theorem volume_maxK_inter_flagM : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ μ, IsGaugeSub (maxK ε ∩ flagM ε W) ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) μ → μ Set.univ = ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) := by
  intro n ε p q hp hq a j W hW μ hμ
  obtain ⟨T, P, Q, hTT, hTo, hTJT, hTP, hTQ, hPP, hQQ, hJP, hJQ, hsum, hmem⟩ :=
    exists_frame n ε p q hp hq a j W hW
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJH : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ' : ∀ {r : ℕ} (X : Matrix (Fin n) (Fin r) ℂ), Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * X) = X := by
    intro r X; rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJP' : ∀ {r : ℕ} (X : Matrix (Fin (p - ∑ i, j i)) (Fin r) ℂ), Formalism.REAL.Jm ε * (P * X) = P * X := by
    intro r X; rw [← Matrix.mul_assoc, hJP]
  have hJQ' : ∀ {r : ℕ} (X : Matrix (Fin (q - ∑ i, j i)) (Fin r) ℂ), Formalism.REAL.Jm ε * (Q * X) = -(Q * X) := by
    intro r X; rw [← Matrix.mul_assoc, hJQ, Matrix.neg_mul]
  have e1 : Pᴴ * Formalism.REAL.Jm ε = Pᴴ := by
    rw [← hJH, ← Matrix.conjTranspose_mul, hJP]
  have e2 : Qᴴ * Formalism.REAL.Jm ε = -Qᴴ := by
    rw [← hJH, ← Matrix.conjTranspose_mul, hJQ, Matrix.conjTranspose_neg]
  have hPT : ∀ k, Pᴴ * T k = 0 := by
    intro k
    have h := congrArg Matrix.conjTranspose (hTP k)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
  have hQT : ∀ k, Qᴴ * T k = 0 := by
    intro k
    have h := congrArg Matrix.conjTranspose (hTQ k)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
  have hPQ : Pᴴ * Q = 0 := by
    have hx : Pᴴ * Q = -(Pᴴ * Q) := by
      calc Pᴴ * Q = Pᴴ * Formalism.REAL.Jm ε * Q := by rw [e1]
        _ = -(Pᴴ * Q) := by rw [Matrix.mul_assoc, hJQ, Matrix.mul_neg]
    ext c d
    have h := congrFun (congrFun hx c) d
    simp only [Matrix.neg_apply] at h
    rw [Matrix.zero_apply]
    linear_combination h / 2
  have hQP : Qᴴ * P = 0 := by
    have h := congrArg Matrix.conjTranspose hPQ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
  let m : Fin a ⊕ (Unit ⊕ Unit) → ℕ := Sum.elim j (Sum.elim (fun _ => p - ∑ i, j i) (fun _ => q - ∑ i, j i))
  let π : Fin a ⊕ (Fin a ⊕ (Unit ⊕ Unit)) → Fin a ⊕ (Unit ⊕ Unit) := Sum.elim Sum.inl (Sum.elim Sum.inl Sum.inr)
  let S : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ := fun s => match s with
    | Sum.inl i => T i
    | Sum.inr (Sum.inl i) => Formalism.REAL.Jm ε * T i
    | Sum.inr (Sum.inr (Sum.inl _)) => P
    | Sum.inr (Sum.inr (Sum.inr _)) => Q
  have hsurj : Function.Surjective π := by
    rintro (i | u)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr (Sum.inr u), rfl⟩
  have horth : ∀ s, (S s)ᴴ * S s = 1 := by
    rintro (i | i | u | u)
    · exact hTT i
    · show (Formalism.REAL.Jm ε * T i)ᴴ * (Formalism.REAL.Jm ε * T i) = 1
      rw [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc, hJJ', hTT]
    · exact hPP
    · exact hQQ
  have hcross : ∀ s t, s ≠ t → (S s)ᴴ * S t = 0 := by
    rintro (i | i | u | u) (k | k | v | v) hst
    · exact hTo i k fun h => hst (h ▸ rfl)
    · show (T i)ᴴ * (Formalism.REAL.Jm ε * T k) = 0
      rw [← Matrix.mul_assoc, hTJT]
    · exact hTP i
    · exact hTQ i
    · show (Formalism.REAL.Jm ε * T i)ᴴ * T k = 0
      rw [Matrix.conjTranspose_mul, hJH, hTJT]
    · show (Formalism.REAL.Jm ε * T i)ᴴ * (Formalism.REAL.Jm ε * T k) = 0
      rw [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc, hJJ', hTo i k fun h => hst (h ▸ rfl)]
    · show (Formalism.REAL.Jm ε * T i)ᴴ * P = 0
      rw [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc, hJP, hTP]
    · show (Formalism.REAL.Jm ε * T i)ᴴ * Q = 0
      rw [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc, hJQ, Matrix.mul_neg, hTQ, neg_zero]
    · exact hPT k
    · show Pᴴ * (Formalism.REAL.Jm ε * T k) = 0
      rw [← Matrix.mul_assoc, e1, hPT]
    · exact absurd (by rw [Subsingleton.elim u v]) hst
    · exact hPQ
    · exact hQT k
    · show Qᴴ * (Formalism.REAL.Jm ε * T k) = 0
      rw [← Matrix.mul_assoc, e2, Matrix.neg_mul, hQT, neg_zero]
    · exact hQP
    · exact absurd (by rw [Subsingleton.elim u v]) hst
  have hsumS : ∑ s, S s * (S s)ᴴ = 1 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    show ∑ i, T i * (T i)ᴴ + (∑ i, (Formalism.REAL.Jm ε * T i) * (Formalism.REAL.Jm ε * T i)ᴴ + (P * Pᴴ + Q * Qᴴ)) = 1
    rw [← hsum]
    simp only [Finset.sum_add_distrib, Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc]
    abel
  have hcomm : ∀ k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ,
      Formalism.REAL.Jm ε * ∑ s, S s * k (π s) * (S s)ᴴ = (∑ s, S s * k (π s) * (S s)ᴴ) * Formalism.REAL.Jm ε := by
    intro k
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    exact levi_lemma (Formalism.REAL.Jm ε) T P Q (fun i => k (Sum.inl i)) (k (Sum.inr (Sum.inl default)))
      (k (Sum.inr (Sum.inr default))) hJJ hJP hJQ e1 e2 hJH
  obtain ⟨Φ, hΦc, hΦi, hΦu, hΦhs⟩ := GlobalTheory.T.exists_blockDiag_unitary_product_hom n ε _ _ π m S hsurj horth hcross hsumS hcomm
  have hform : ∀ x : ∀ i, Formalism.REAL.UJ (allPos (m i)), uMat (Φ x) =
      (∑ i, (T i * (show Matrix (Fin (j i)) (Fin (j i)) ℂ from uMat (x (Sum.inl i))) * (T i)ᴴ +
        Formalism.REAL.Jm ε * T i * (show Matrix (Fin (j i)) (Fin (j i)) ℂ from uMat (x (Sum.inl i))) * (T i)ᴴ * Formalism.REAL.Jm ε)) +
      P * (show Matrix (Fin (p - ∑ i, j i)) (Fin (p - ∑ i, j i)) ℂ from uMat (x (Sum.inr (Sum.inl default)))) * Pᴴ + Q * (show Matrix (Fin (q - ∑ i, j i)) (Fin (q - ∑ i, j i)) ℂ from uMat (x (Sum.inr (Sum.inr default)))) * Qᴴ := by
    intro x
    rw [hΦu]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    show ∑ i, T i * (show Matrix (Fin (j i)) (Fin (j i)) ℂ from uMat (x (Sum.inl i))) * (T i)ᴴ + (∑ i, (Formalism.REAL.Jm ε * T i) * (show Matrix (Fin (j i)) (Fin (j i)) ℂ from uMat (x (Sum.inl i))) * (Formalism.REAL.Jm ε * T i)ᴴ +
        (P * (show Matrix (Fin (p - ∑ i, j i)) (Fin (p - ∑ i, j i)) ℂ from uMat (x (Sum.inr (Sum.inl default)))) * Pᴴ + Q * (show Matrix (Fin (q - ∑ i, j i)) (Fin (q - ∑ i, j i)) ℂ from uMat (x (Sum.inr (Sum.inr default)))) * Qᴴ)) = _
    simp only [Finset.sum_add_distrib, Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc]
    abel
  have hrange : Set.range Φ = maxK ε ∩ flagM ε W := by
    ext g
    rw [GlobalTheory.T.mem_maxCompact_inter_levi_iff_frame n ε a j W _ _ T P Q ⟨hTT, hTo, hTJT, hTP, hTQ, hPP, hQQ, hJP, hJQ, hsum, hmem⟩ g]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fun i => x (Sum.inl i), x (Sum.inr (Sum.inl default)), x (Sum.inr (Sum.inr default)), hform x⟩
    · rintro ⟨k, u, v, hg⟩
      let x : ∀ i, Formalism.REAL.UJ (allPos (m i)) := fun i => match i with
        | Sum.inl i => k i
        | Sum.inr (Sum.inl _) => u
        | Sum.inr (Sum.inr _) => v
      refine ⟨x, Subtype.ext (Units.ext ?_)⟩
      show uMat (Φ x) = uMat g
      rw [hform x, hg]
  have hd : (p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2 = ∑ i, m i ^ 2 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, m, Sum.elim_inl, Sum.elim_inr]
    ring
  have hμ' : IsGaugeSub (Set.range Φ) (∑ i, m i ^ 2) μ := by
    rw [hrange, ← hd]; exact hμ
  let w : Fin a ⊕ (Unit ⊕ Unit) → ℝ := Sum.elim (fun _ => 2) (fun _ => 1)
  have hw : ∀ i, 0 < w i := by
    rintro (i | u | u) <;> norm_num [w]
  have hhs : ∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ i, w i * Formalism.REAL.hs (uMat (g i) - 1) := by
    intro g
    rw [hΦhs]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    dsimp only [π, w, m, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.mul_sum, two_mul, one_mul, one_mul, add_assoc]
    rfl
  rw [volume_range n ε _ m w Φ hw hΦc hΦi hhs μ hμ']
  congr 1
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, m, w, Sum.elim_inl, Sum.elim_inr, Real.one_rpow,
    mul_one]
  ring

end GlobalTheory.FlagMeas.LeviCompact
