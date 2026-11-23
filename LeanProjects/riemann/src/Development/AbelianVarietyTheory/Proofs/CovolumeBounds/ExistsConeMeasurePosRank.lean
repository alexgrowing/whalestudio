import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate

noncomputable section

namespace GlobalTheory.HCXi.ConeOne

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8

def radMeas (N : ℕ) : Measure ℂ := (volume : Measure ℂ).withDensity fun c => ENNReal.ofReal (‖c‖ ^ (2 * N))

instance (N : ℕ) : SFinite (radMeas N) := by unfold radMeas; infer_instance

lemma radMeas_map (N : ℕ) (t : ℝ) (ht : 0 < t) :
    (radMeas N).map (fun c => (t : ℂ) * c) = ENNReal.ofReal ((t ^ (2 * N + 2))⁻¹) • radMeas N := by
  have hm : Measurable (fun c : ℂ => (t : ℂ) * c) := measurable_const_mul _
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hw : Measurable fun c : ℂ => ENNReal.ofReal (‖c‖ ^ (2 * N)) := by fun_prop
  rw [lintegral_map hg hm, lintegral_smul_measure]
  unfold radMeas
  have hgl : Measurable fun a : ℂ => g ((t : ℂ) * a) := hg.comp hm
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hg, lintegral_withDensity_eq_lintegral_mul _ hw hgl]
  have hmap : (volume : Measure ℂ).map (fun c => (t : ℂ) * c) = ENNReal.ofReal ((t ^ 2)⁻¹) • volume := by
    have h := Measure.map_addHaar_smul (volume : Measure ℂ) ht.ne'
    rw [Complex.finrank_real_complex, abs_of_pos (by positivity)] at h
    exact h
  have h1 := lintegral_map (μ := (volume : Measure ℂ)) (hw.mul hg) hm
  rw [hmap, lintegral_smul_measure] at h1
  have h2 : ∀ c : ℂ, ((fun c : ℂ => ENNReal.ofReal (‖c‖ ^ (2 * N))) * fun a => g ((t : ℂ) * a)) c =
      ENNReal.ofReal ((t ^ (2 * N))⁻¹) * (ENNReal.ofReal (‖(t : ℂ) * c‖ ^ (2 * N)) * g ((t : ℂ) * c)) := by
    intro c
    rw [Pi.mul_apply, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.le, mul_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  rw [lintegral_congr h2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [Pi.mul_apply] at h1 ⊢
  rw [← h1, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← mul_inv, ← pow_add]

def par (k r' : ℕ) (p : ℂ × HPar k r') : Fin (2 * (1 + r') + k + 1) → ℂ :=
  p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r')

lemma par_meas (k r' : ℕ) : Measurable (par k r') := by
  have : par k r' = Ψt k r' ∘ cm1Θ k r' := funext fun p => parametrisation_eq_scaled_sum p
  rw [this]
  exact Ψt_meas.comp parametrisation_map_measurable

lemma cone_def (k r' : ℕ) :
    coneMeas k r' = ((radMeas (2 * r' + k + 1)).prod (volume : Measure (HPar k r'))).map (par k r') := rfl

instance hparSFinite (k r' : ℕ) : SFinite (volume : Measure (HPar k r')) := by
  rw [Measure.volume_eq_prod]; infer_instance

lemma cone_sfinite (k r' : ℕ) : SFinite (coneMeas k r') := by
  rw [cone_def]; infer_instance

lemma cone_map (k r' : ℕ) (t : ℝ) (ht : 0 < t) :
    (coneMeas k r').map (fun v => (t : ℂ) • v) =
      ENNReal.ofReal ((t ^ (2 * (2 * r' + k + 1) + 2))⁻¹) • coneMeas k r' := by
  have hm : Measurable (fun c : ℂ => (t : ℂ) * c) := measurable_const_mul _
  have hs : Measurable (fun v : Fin (2 * (1 + r') + k + 1) → ℂ => (t : ℂ) • v) := measurable_const_smul _
  rw [cone_def, Measure.map_map hs (par_meas k r')]
  have e : (fun v : Fin (2 * (1 + r') + k + 1) → ℂ => (t : ℂ) • v) ∘ par k r' =
      par k r' ∘ Prod.map (fun c : ℂ => (t : ℂ) * c) id := by
    funext p
    simp only [Function.comp, par, Prod.map, id, smul_smul]
  rw [e, ← Measure.map_map (par_meas k r') (hm.prodMap measurable_id), ← Measure.map_prod_map _ _ hm measurable_id,
    radMeas_map _ t ht, Measure.map_id, Measure.prod_smul_left, Measure.map_smul]

lemma sqLen_cont {n : ℕ} : Continuous (sqLen : (Fin n → ℂ) → ℝ) := by
  unfold sqLen
  fun_prop

lemma sqLen_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ sqLen v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma sqLen_smul {n : ℕ} (t : ℝ) (v : Fin n → ℂ) : sqLen ((t : ℂ) • v) = t ^ 2 * sqLen v := by
  unfold sqLen
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, Complex.normSq_ofReal, sq]

lemma cone_homog (k r' : ℕ) (s : ℝ) (hs : 0 < s) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, f (s * sqLen v) ∂(coneMeas k r')) =
      ENNReal.ofReal (s ^ (-((2 * (1 + r') + k : ℕ) : ℝ))) * ∫⁻ v, f (sqLen v) ∂(coneMeas k r') := by
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsm : Measurable (fun v : Fin (2 * (1 + r') + k + 1) → ℂ => ((Real.sqrt s : ℝ) : ℂ) • v) :=
    measurable_const_smul _
  have h1 := lintegral_map (μ := coneMeas k r') (hf.comp sqLen_cont.measurable) hsm
  rw [cone_map k r' _ ht, lintegral_smul_measure] at h1
  simp only [Function.comp, sqLen_smul, Real.sq_sqrt hs.le] at h1
  rw [← h1, smul_eq_mul]
  congr 2
  rw [Real.rpow_neg hs.le, Real.rpow_natCast,
    show 2 * (2 * r' + k + 1) + 2 = 2 * (2 * (1 + r') + k) by ring, pow_mul, Real.sq_sqrt hs.le]

lemma par_eq (k r' : ℕ) (p : ℂ × HPar k r') :
    par k r' p = p.1 • mk3 k r' (hb k r' p.2.1 p.2.2) p.2.1 1 := by
  unfold par mk3
  congr 1
  rw [one_smul]
  abel

lemma cone_ae (k r' : ℕ) : ∀ᵐ v ∂(coneMeas k r'), v ≠ 0 ∧ herm (Hpk k (1 + r')) v v = 0 := by
  rw [cone_def]
  have hc : Continuous fun v : Fin (2 * (1 + r') + k + 1) → ℂ => herm (Hpk k (1 + r')) v v :=
    hermitian_quadratic_continuous (k := k) (r' := 1 + r')
  have hS : MeasurableSet {v : Fin (2 * (1 + r') + k + 1) → ℂ | v ≠ 0 ∧ herm (Hpk k (1 + r')) v v = 0} :=
    (MeasurableSet.singleton 0).compl.inter (isClosed_eq hc continuous_const).measurableSet
  rw [ae_map_iff (par_meas k r').aemeasurable hS]
  have h0 : ∀ᵐ p : ℂ × HPar k r' ∂((radMeas (2 * r' + k + 1)).prod (volume : Measure (HPar k r'))), p.1 ≠ 0 := by
    rw [ae_iff]
    have : {p : ℂ × HPar k r' | ¬ p.1 ≠ 0} = {(0 : ℂ)} ×ˢ Set.univ := by
      ext p; simp
    rw [this, Measure.prod_prod]
    have h0 : radMeas (2 * r' + k + 1) {(0 : ℂ)} = 0 := by
      unfold radMeas
      exact withDensity_absolutelyContinuous _ _ (by simp)
    rw [h0, zero_mul]
  filter_upwards [h0] with p hp
  rw [par_eq]
  constructor
  · intro h
    apply hp
    have := congrArg cL h
    rw [three_block_smul, three_block_last, mul_one] at this
    exact this
  · rw [herm_smul_left, herm_smul_right, hermitian_three_block]
    have := hb_add_conj (k := k) (r' := r') p.2.1 p.2.2
    simp only [map_one, mul_one, one_mul]
    rw [this]
    simp

lemma cone_ne_zero (k r' : ℕ) : coneMeas k r' ≠ 0 := by
  intro h
  have h1 : coneMeas k r' Set.univ = 0 := by rw [h]; rfl
  rw [cone_def, Measure.map_apply (par_meas k r') MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · unfold radMeas at h1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_eq_zero_iff (by fun_prop)] at h1
    have h2 : ∀ᵐ c : ℂ, c ≠ 0 := by rw [ae_iff]; simp
    have h3 : ∀ᵐ _c : ℂ, False := by
      filter_upwards [h1, h2] with c hc hc0
      have : 0 < ‖c‖ ^ (2 * (2 * r' + k + 1)) := pow_pos (norm_pos_iff.2 hc0) _
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hc
      linarith
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h3
    exact NeZero.ne _ h3
  · rw [Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact (isOpen_univ.measure_pos (volume : Measure (Fin (2 * r' + k + 1) → ℂ)) Set.univ_nonempty).ne' h1
    · simp at h1

lemma ball_compact {n : ℕ} : IsCompact {v : Fin n → ℂ | sqLen v ≤ 1} := by
  refine (isCompact_closedBall (0 : Fin n → ℂ) 1).of_isClosed_subset (isClosed_le sqLen_cont continuous_const) ?_
  intro v hv
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h1 : Complex.normSq (v i) ≤ sqLen v :=
    Finset.single_le_sum (f := fun i => Complex.normSq (v i)) (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have h2 : sqLen v ≤ 1 := hv
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (v i)]

lemma gauss_finite {X : Type*} [MeasurableSpace X] (m : Measure X) (q : X → ℝ) (hq : Measurable q) (h0 : ∀ v, 0 ≤ q v)
    (d : ℕ) (hh : ∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ v, f (s * q v) ∂m) = ENNReal.ofReal (s ^ (-(d : ℝ))) * ∫⁻ v, f (q v) ∂m)
    (hfin : m {v | q v ≤ 1} < ∞) : (∫⁻ v, ENNReal.ofReal (Real.exp (-q v)) ∂m) ≠ ∞ := by
  set f : ℝ → ℝ≥0∞ := (Set.Iic (1 : ℝ)).indicator 1 with hf
  have hfm : Measurable f := measurable_const.indicator measurableSet_Iic
  have hM : (∫⁻ v, f (q v) ∂m) = m {v | q v ≤ 1} := by
    rw [← lintegral_indicator_one (measurableSet_le hq measurable_const)]
    rfl
  have hle : ∀ v, ENNReal.ofReal (Real.exp (-q v)) ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ))) * f (((n : ℝ) + 1)⁻¹ * q v) := by
    intro v
    refine le_trans ?_ (ENNReal.le_tsum ⌊q v⌋₊)
    have h1 : ((⌊q v⌋₊ : ℝ) + 1)⁻¹ * q v ≤ 1 := by
      rw [inv_mul_le_iff₀ (by positivity), mul_one]
      exact (Nat.lt_floor_add_one _).le
    rw [hf, Set.indicator_of_mem (show _ ∈ Set.Iic (1 : ℝ) from h1), Pi.one_apply, mul_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg (Nat.floor_le (h0 v))))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun v => ENNReal.ofReal (Real.exp (-(n : ℝ))) * f (((n : ℝ) + 1)⁻¹ * q v)) m :=
    fun n => ((hfm.comp (hq.const_mul _)).const_mul _).aemeasurable
  rw [lintegral_tsum hmeas]
  have hterm : ∀ n : ℕ, (∫⁻ v, ENNReal.ofReal (Real.exp (-(n : ℝ))) * f (((n : ℝ) + 1)⁻¹ * q v) ∂m) =
      ENNReal.ofReal (Real.exp (-(n : ℝ)) * ((n : ℝ) + 1) ^ d) * m {v | q v ≤ 1} := by
    intro n
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hh _ (by positivity) f hfm, hM, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow, inv_inv]
  simp only [hterm]
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_ne_top ?_ hfin.ne
  have hsum : Summable fun n : ℕ => Real.exp (-(n : ℝ)) * ((n : ℝ) + 1) ^ d := by
    have h1 := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul d (r := 1) one_pos)
    refine (h1.mul_left (Real.exp 1)).congr fun n => ?_
    push_cast
    rw [mul_left_comm, ← Real.exp_add, mul_comm]
    congr 2
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

end GlobalTheory.HCXi.ConeOne

namespace GlobalTheory.HCXi

open ConeOne Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8

theorem exists_cone_measure_pos_rank : ∀ k r' : ℕ, ∃ m : Measure (Fin (2 * (1 + r') + k + 1) → ℂ), SFinite m ∧ (∀ᵐ v ∂m, v ≠ 0 ∧ herm (Hpk k (1 + r')) v v = 0) ∧ (∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f → (∫⁻ v, f (s * sqLen v) ∂m) = ENNReal.ofReal (s ^ (-((2 * (1 + r') + k : ℕ) : ℝ))) * ∫⁻ v, f (sqLen v) ∂m) ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ 0 ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ ∞ ∧ ∀ g ∈ GV k (1 + r'), (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ v))) ∂m) = ∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m := by
  intro k r'
  have hG : Measurable fun v : Fin (2 * (1 + r') + k + 1) → ℂ => ENNReal.ofReal (Real.exp (-sqLen v)) :=
    (Real.measurable_exp.comp sqLen_cont.measurable.neg).ennreal_ofReal
  refine ⟨coneMeas k r', cone_sfinite k r', cone_ae k r', cone_homog k r', ?_, ?_, ?_⟩
  · intro h
    rw [lintegral_eq_zero_iff hG] at h
    apply cone_ne_zero k r'
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h] with v hv
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hv
    exact absurd hv (not_le.2 (Real.exp_pos _))
  · exact gauss_finite _ _ sqLen_cont.measurable sqLen_nonneg _ (cone_homog k r')
      (isotropic_cone_finite_measure k r' _ ball_compact)
  · intro g hg
    have h1 := lintegral_map (μ := coneMeas k r') hG (cf_mulVec_meas g)
    rw [isotropic_cone_invariance k r' g hg] at h1
    exact h1.symm

end GlobalTheory.HCXi
