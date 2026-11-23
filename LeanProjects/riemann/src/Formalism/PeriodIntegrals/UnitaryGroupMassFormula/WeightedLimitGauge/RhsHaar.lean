import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def RhsWInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ s ∈ UWb k r, ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      rhsW k r z z' μW μW' μsec (fun x => φ (lmulM s x)) = rhsW k r z z' μW μW' μsec φ

namespace ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def secP (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  if Tz k r z * Tz k r z' < Complex.normSq ζ then μsec ζ else 1

def wD (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : ℝ≥0∞ :=
  if Tz k r z * Tz k r z' < Complex.normSq ζ then ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) else 0

def chartF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (q : ℂ × Mt k r × Mt k r) : Mt k r :=
  fun i j => (Matrix.of q.2.1 * embWb k r (secP k r z z' μsec q.1) * (Matrix.of q.2.2)⁻¹) i j

def srcM (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) :
    Measure (ℂ × Mt k r × Mt k r) :=
  ((volume : Measure ℂ).withDensity (wD k r z z')).prod (μW.prod μW')

def nuR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Measure (Mt k r) :=
  (srcM k r z z' μW μW').map (chartF k r z z' μsec)

def zF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : ℂ := herm (Hpk k r) (Matrix.of x *ᵥ z') z

def goodS (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (ℂ × Mt k r × Mt k r) :=
  {q | Tz k r z * Tz k r z' < Complex.normSq q.1 ∧ Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ UWset k r z'}

theorem meas_wD : Measurable (wD k r z z') := by
  have hn : Measurable (fun ζ : ℂ => Complex.normSq ζ) := Complex.continuous_normSq.measurable
  have hz : Measurable (zWeight k (Tz k r z) (Tz k r z')) := by
    unfold zWeight
    exact Measurable.ite (measurableSet_le measurable_const hn) ((hn.sub measurable_const).pow_const _)
      measurable_const
  unfold wD
  exact Measurable.ite (measurableSet_lt measurable_const hn) (ENNReal.measurable_ofReal.comp hz) measurable_const

theorem meas_secP (hs : IsSection k r z z' μsec) :
    Measurable (fun ζ : ℂ => (fun i j => secP k r z z' μsec ζ i j : Fin (k + 1) → Fin (k + 1) → ℂ)) := by
  have e : (fun ζ : ℂ => (fun i j => secP k r z z' μsec ζ i j : Fin (k + 1) → Fin (k + 1) → ℂ)) =
      {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}.piecewise
        (fun ζ => (fun i j => μsec ζ i j : Fin (k + 1) → Fin (k + 1) → ℂ))
        (fun _ => (fun i j => (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j)) := by
    funext ζ
    by_cases h : Tz k r z * Tz k r z' < Complex.normSq ζ <;> simp [secP, Set.piecewise, h]
  rw [e]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const
    (isOpen_lt continuous_const Complex.continuous_normSq).measurableSet
  exact continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hs.1 i j).continuousOn

theorem cont_emb : Continuous (embWb k r) := by
  have e : embWb k r = fun μ => MB.Em k r * μ * (MB.Em k r)ᵀ + (1 - MB.Em k r * (MB.Em k r)ᵀ) :=
    funext fun μ => MB.emb_eq μ
  rw [e]
  exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).add continuous_const

theorem meas_invM : Measurable (HU.invM : Mt k r → Mt k r) := by
  rw [HU.invM_smul]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (measurable_inv.comp HU.detF_cont.measurable).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp HU.adjF_cont.measurable))

def gC (k r : ℕ) (p : (Fin (k + 1) → Fin (k + 1) → ℂ) × Mt k r × Mt k r) : Mt k r :=
  fun i j => (Matrix.of p.2.1 * embWb k r (Matrix.of p.1) * Matrix.of p.2.2) i j

theorem cont_gC : Continuous (gC k r) := by
  have hA : Continuous (fun p : (Fin (k + 1) → Fin (k + 1) → ℂ) × Mt k r × Mt k r => (Matrix.of p.2.1 : Mat k r)) :=
    continuous_fst.comp continuous_snd
  have hB : Continuous (fun p : (Fin (k + 1) → Fin (k + 1) → ℂ) × Mt k r × Mt k r =>
      embWb k r (Matrix.of p.1)) := cont_emb.comp continuous_fst
  have hC : Continuous (fun p : (Fin (k + 1) → Fin (k + 1) → ℂ) × Mt k r × Mt k r => (Matrix.of p.2.2 : Mat k r)) :=
    continuous_snd.comp continuous_snd
  exact continuous_pi fun i => continuous_pi fun j => ((hA.matrix_mul hB).matrix_mul hC).matrix_elem i j

theorem meas_chartF (hs : IsSection k r z z' μsec) : Measurable (chartF k r z z' μsec) := by
  have h := (cont_gC (k := k) (r := r)).measurable.comp (((meas_secP hs).comp measurable_fst).prodMk
    ((measurable_fst.comp measurable_snd).prodMk (meas_invM.comp (measurable_snd.comp measurable_snd))))
  exact h

theorem cont_zF : Continuous (zF k r z z') := by
  have hid : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  show Continuous (fun x : Mt k r => star z ⬝ᵥ (Hpk k r *ᵥ (Matrix.of x *ᵥ z')))
  exact Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const
    (Continuous.matrix_mulVec hid continuous_const))

theorem herm_fix {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * H * g = H) (w : Fin n → ℂ)
    (hw : g *ᵥ w = w) (v : Fin n → ℂ) : herm H (g *ᵥ v) w = herm H v w := by
  unfold herm
  conv_lhs => rw [← hw]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem inWb_eq {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) : MB.Em k r *ᵥ wbPart k r w = w := by
  ext i
  simp only [Matrix.mulVec, dotProduct, MB.Em, wbPart, ite_mul, one_mul, zero_mul]
  by_cases hi : MB.mid k r i
  · rw [Finset.sum_eq_single (MB.midx hi)]
    · rw [if_pos (MB.wI_midx hi).symm, MB.wI_midx hi]
    · intro m _ hm
      rw [if_neg]
      intro h
      exact hm (MB.wI_inj (h.symm.trans (MB.wI_midx hi).symm))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · refine (hw i ?_).symm
      simp only [MB.mid, not_and_or, not_le] at hi
      omega
    · intro m _
      rw [if_neg]
      intro h
      exact hi (by rw [h]; exact MB.mid_wI m)

theorem emb_mul_Em (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ * MB.Em k r = MB.Em k r * μ := by
  rw [MB.emb_eq, Matrix.add_mul, MB.Q_Em, add_zero, Matrix.mul_assoc, MB.EmT_Em, Matrix.mul_one]

theorem hpk_chain (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    Hpk k r *ᵥ (embWb k r μ *ᵥ (MB.Em k r *ᵥ u)) = MB.Em k r *ᵥ (Hb k *ᵥ (μ *ᵥ u)) := by
  rw [Matrix.mulVec_mulVec u (embWb k r μ) (MB.Em k r), emb_mul_Em, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec _ (Hpk k r) (MB.Em k r), MB.Hpk_Em, ← Matrix.mulVec_mulVec]

theorem em_dot (u : Fin (k + 1) → ℂ) (Y : Fin (k + 1) → ℂ) :
    star (MB.Em k r *ᵥ u) ⬝ᵥ (MB.Em k r *ᵥ Y) = star u ⬝ᵥ Y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, MB.Em_conjT, MB.EmT_Em,
    Matrix.one_mulVec]

theorem herm_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (embWb k r μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  conv_lhs => rw [← inWb_eq hz, ← inWb_eq hz']
  unfold herm
  rw [hpk_chain, em_dot]

theorem secP_eq {ζ : ℂ} (h : Tz k r z * Tz k r z' < Complex.normSq ζ) : secP k r z z' μsec ζ = μsec ζ := by
  unfold secP
  exact if_pos h

theorem zF_chart (hD : WbData k r z z' μW μW' a a' μsec) {q : ℂ × Mt k r × Mt k r} (hq : q ∈ goodS k r z z') :
    zF k r z z' (chartF k r z z' μsec q) = q.1 := by
  obtain ⟨hζ, hh, hh'⟩ := hq
  have hu' := HU.isUnit_of_uh hh'.1
  have hinv : (Matrix.of q.2.2 : Mat k r)⁻¹ *ᵥ z' = z' := by
    conv_lhs => rw [← hh'.2.2]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu', Matrix.one_mulVec]
  show herm (Hpk k r) ((Matrix.of q.2.1 * embWb k r (secP k r z z' μsec q.1) * (Matrix.of q.2.2)⁻¹) *ᵥ z') z = q.1
  rw [← Matrix.mulVec_mulVec, hinv, ← Matrix.mulVec_mulVec, herm_fix (Hpk k r) (Matrix.of q.2.1) hh.1 z hh.2.2,
    secP_eq hζ, herm_emb _ hD.z_mem hD.z'_mem]
  exact (hD.sec.2 q.1 hζ).2

theorem mem_chart (hD : WbData k r z z' μW μW' a a' μsec) {q : ℂ × Mt k r × Mt k r} (hq : q ∈ goodS k r z z') :
    Matrix.of (chartF k r z z' μsec q) ∈ UWb k r := by
  obtain ⟨hζ, hh, hh'⟩ := hq
  have sub : ∀ {w : Fin (2 * r + k + 1) → ℂ} {g : Mat k r}, g ∈ UWset k r w → g ∈ UWb k r :=
    fun hg => ⟨hg.1, hg.2.1⟩
  show Matrix.of q.2.1 * embWb k r (secP k r z z' μsec q.1) * (Matrix.of q.2.2)⁻¹ ∈ UWb k r
  rw [secP_eq hζ]
  exact HU.uwb_mul (HU.uwb_mul (sub hh) (MB.emb_mem_UWb (hD.sec.2 q.1 hζ).1)) (HU.uwb_inv (sub hh'))

theorem wD_zero_off {ζ : ℂ} (h : ¬ Tz k r z * Tz k r z' < Complex.normSq ζ) : wD k r z z' ζ = 0 := by
  unfold wD
  exact if_neg h

theorem src_null (hD : WbData k r z z' μW μW' a a' μsec) : srcM k r z z' μW μW' (goodS k r z z')ᶜ = 0 := by
  have := hD.haarW.1
  have := hD.haarW'.1
  have h1 : (volume : Measure ℂ).withDensity (wD k r z z')
      {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}ᶜ = 0 := by
    rw [withDensity_apply_eq_zero' meas_wD.aemeasurable]
    exact measure_mono_null (fun ζ hζ => (hζ.1 (wD_zero_off hζ.2)).elim) measure_empty
  have hsub : (goodS k r z z')ᶜ ⊆
      ({ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}ᶜ ×ˢ Set.univ) ∪
        (Set.univ ×ˢ ({x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ)) ∪
        (Set.univ ×ˢ (Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ UWset k r z'})) := by
    intro q hq
    simp only [goodS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or] at hq
    rcases hq with h | h | h
    · exact Or.inl (Or.inl ⟨h, trivial⟩)
    · exact Or.inl (Or.inr ⟨trivial, h, trivial⟩)
    · exact Or.inr ⟨trivial, trivial, h⟩
  refine measure_mono_null hsub (measure_union_null (measure_union_null ?_ ?_) ?_)
  · rw [srcM, Measure.prod_prod, h1, zero_mul]
  · rw [srcM, Measure.prod_prod, Measure.prod_prod, hD.haarW.2.2.1, zero_mul, mul_zero]
  · rw [srcM, Measure.prod_prod, Measure.prod_prod, hD.haarW'.2.2.1, mul_zero, mul_zero]

theorem circle_ae (c : ℝ) : ∀ᵐ ζ : ℂ ∂volume, Complex.normSq ζ ≠ c := by
  rw [ae_iff]
  refine measure_mono_null (fun ζ hζ => ?_) (Measure.addHaar_sphere (volume : Measure ℂ) (0 : ℂ) (Real.sqrt c))
  simp only [Set.mem_ofPred_eq, not_not] at hζ
  rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem repr (hD : WbData k r z z' μW μW' a a' μsec) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    rhsW k r z z' μW μW' μsec φ = ∫⁻ x, φ x ∂nuR k r z z' μW μW' μsec := by
  have := hD.haarW.1
  have := hD.haarW'.1
  have hF := meas_chartF hD.sec
  have hΦ : Measurable (fun q => φ (chartF k r z z' μsec q)) := hφ.comp hF
  rw [nuR, lintegral_map hφ hF, srcM, lintegral_prod _ hΦ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ meas_wD hΦ.lintegral_prod_right']
  unfold rhsW
  apply lintegral_congr_ae
  filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun y : Mt k r × Mt k r => φ (chartF k r z z' μsec (ζ, y)))
    (hΦ.comp measurable_prodMk_left).aemeasurable]
  by_cases h : Tz k r z * Tz k r z' < Complex.normSq ζ
  · have hw : wD k r z z' ζ = ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) := by
      unfold wD
      exact if_pos h
    rw [hw]
    congr 1
    refine lintegral_congr fun x => lintegral_congr fun y => ?_
    have hc : chartF k r z z' μsec (ζ, x, y) =
        fun i j => (Matrix.of x * embWb k r (μsec ζ) * (Matrix.of y)⁻¹) i j := by
      unfold chartF
      rw [secP_eq h]
    exact congrArg φ hc.symm
  · have hlt : Complex.normSq ζ < Tz k r z * Tz k r z' := lt_of_le_of_ne (not_lt.1 h) hζ
    have hz : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
      unfold zWeight
      exact if_neg (not_le.2 hlt)
    rw [wD_zero_off h, hz, ENNReal.ofReal_zero, zero_mul, zero_mul]

theorem wvol_lt (hT : 0 ≤ Tz k r z * Tz k r z') (n : ℕ) :
    (volume : Measure ℂ).withDensity (wD k r z z') (Metric.closedBall 0 n) < ⊤ := by
  rw [withDensity_apply _ measurableSet_closedBall]
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_closedBall
    (g := fun _ => ENNReal.ofReal (((n : ℝ) ^ 2) ^ (k - 1))) ?_) ?_
  · intro ζ hζ
    unfold wD
    split_ifs with h
    · apply ENNReal.ofReal_le_ofReal
      unfold zWeight
      rw [if_pos h.le]
      have h1 : Complex.normSq ζ ≤ (n : ℝ) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 hζ) 2
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    · simp
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

theorem nu_aSet_lt (hD : WbData k r z z' μW μW' a a' μsec) (n : ℕ) :
    nuR k r z z' μW μW' μsec {x | ‖zF k r z z' x‖ ≤ n} < ⊤ := by
  have := hD.haarW.1
  have := hD.haarW'.1
  have hF := meas_chartF hD.sec
  have hA : MeasurableSet {x : Mt k r | ‖zF k r z z' x‖ ≤ n} :=
    (isClosed_le cont_zF.norm continuous_const).measurableSet
  rw [nuR, Measure.map_apply hF hA]
  have hsub : chartF k r z z' μsec ⁻¹' {x | ‖zF k r z z' x‖ ≤ n} ⊆
      (Metric.closedBall (0 : ℂ) n ×ˢ Set.univ) ∪ (goodS k r z z')ᶜ := by
    intro q hq
    by_cases hg : q ∈ goodS k r z z'
    · left
      refine ⟨?_, trivial⟩
      have hq' : ‖q.1‖ ≤ n := by
        rw [← zF_chart hD hg]
        exact hq
      exact mem_closedBall_zero_iff.2 hq'
    · exact Or.inr hg
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
  rw [src_null hD, add_zero, srcM, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod, hD.massW,
    hD.massW']
  exact ENNReal.mul_lt_top (wvol_lt (mul_pos hD.T_pos hD.T'_pos).le n)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

theorem nu_sigmaFinite (hD : WbData k r z z' μW μW' a a' μsec) : SigmaFinite (nuR k r z z' μW μW' μsec) := by
  refine ⟨⟨⟨fun n => {x | ‖zF k r z z' x‖ ≤ (n : ℝ)}, fun _ => trivial, fun n => nu_aSet_lt hD n, ?_⟩⟩⟩
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := exists_nat_ge ‖zF k r z z' x‖
  exact ⟨n, hn⟩

theorem nu_ne_zero (hD : WbData k r z z' μW μW' a a' μsec) : nuR k r z z' μW μW' μsec ≠ 0 := by
  have := hD.haarW.1
  have := hD.haarW'.1
  intro h0
  have h1 : nuR k r z z' μW μW' μsec Set.univ = 0 := by rw [h0]; rfl
  rw [nuR, Measure.map_apply (meas_chartF hD.sec) MeasurableSet.univ, Set.preimage_univ, srcM,
    ← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod, hD.massW, hD.massW'] at h1
  rcases mul_eq_zero.1 h1 with h | h
  · have hc : 0 ≤ Tz k r z * Tz k r z' := (mul_pos hD.T_pos hD.T'_pos).le
    have hEo : IsOpen {ζ : ℂ | Tz k r z * Tz k r z' + 1 < Complex.normSq ζ} :=
      isOpen_lt continuous_const Complex.continuous_normSq
    have hEn : ({ζ : ℂ | Tz k r z * Tz k r z' + 1 < Complex.normSq ζ}).Nonempty := by
      refine ⟨((Tz k r z * Tz k r z' + 2 : ℝ) : ℂ), ?_⟩
      show Tz k r z * Tz k r z' + 1 < Complex.normSq _
      rw [Complex.normSq_ofReal]
      nlinarith
    have hE := hEo.measure_pos (volume : Measure ℂ) hEn
    have hle : volume {ζ : ℂ | Tz k r z * Tz k r z' + 1 < Complex.normSq ζ} ≤
        (volume : Measure ℂ).withDensity (wD k r z z') {ζ : ℂ | Tz k r z * Tz k r z' + 1 < Complex.normSq ζ} := by
      rw [withDensity_apply _ hEo.measurableSet, ← setLIntegral_one]
      refine setLIntegral_mono' hEo.measurableSet fun ζ hζ => ?_
      have hζ' : Tz k r z * Tz k r z' + 1 < Complex.normSq ζ := hζ
      have hD' : Tz k r z * Tz k r z' < Complex.normSq ζ := by linarith
      unfold wD zWeight
      rw [if_pos hD', if_pos hD'.le, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith))
    exact (ne_of_gt (lt_of_lt_of_le hE (hle.trans (measure_mono (Set.subset_univ _))))) h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 hD.a_pos)
    · exact absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 hD.a'_pos)

theorem nu_inv (hInv : RhsWInv) (hD : WbData k r z z' μW μW' a a' μsec) (s : Mat k r) (hs : s ∈ UWb k r) :
    (nuR k r z z' μW μW' μsec).map (lmulM s) = nuR k r z z' μW μW' μsec := by
  have hl : Measurable (lmulM s : Mt k r → Mt k r) := (HU.lmulM_cont s).measurable
  ext A hA
  have e : ((lmulM s) ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) = fun x => A.indicator 1 (lmulM s x) := by
    funext x
    rfl
  rw [Measure.map_apply hl hA, ← lintegral_indicator_one (hl hA), ← lintegral_indicator_one hA,
    ← repr hD _ (measurable_one.indicator (hl hA)), ← repr hD _ (measurable_one.indicator hA), e,
    hInv k r z z' μW μW' a a' μsec hD s hs _ (measurable_one.indicator hA)]

theorem nu_ball (hD : WbData k r z z' μW μW' a a' μsec) :
    ∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → nuR k r z z' μW μW' μsec (bBall k r ρ) < ⊤ := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
    ((((isCompact_closedBall (0 : lieE (UWb k r)) 1).image (continuous_expChart k r (UWb k r))).image
      cont_zF).isBounded)
  obtain ⟨n, hn⟩ := exists_nat_ge C
  refine ⟨1, one_pos, fun ρ hρ hρ1 => lt_of_le_of_lt (measure_mono ?_) (nu_aSet_lt hD n)⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (hC _ ⟨_, ⟨y, Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ1.le hy), rfl⟩, rfl⟩).trans hn

end ZetaZeros

open ZetaZeros in

theorem rhsHaar_of (hInv : RhsWInv) : RhsHaar := by
  intro k r z z' μW μW' a a' μsec hD
  have := hD.haarW.1
  have := hD.haarW'.1
  refine ⟨nuR k r z z' μW μW' μsec, ⟨nu_sigmaFinite hD, nu_ne_zero hD, ?_, fun s hs => nu_inv hInv hD s hs⟩,
    nu_ball hD, fun φ hφ => repr hD φ hφ⟩
  rw [nuR, Measure.map_apply (meas_chartF hD.sec) (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
    HU.amb_closed.isOpen_compl.measurableSet]
  exact measure_mono_null (fun q hq hg => hq (mem_chart hD hg)) (src_null hD)

end PI.RhsWLim.W
