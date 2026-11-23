import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace GlobalTheory.HypOrbitUnique

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU PI.RhsWLim.W.MB

theorem fubini_identity {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    [MeasurableSpace X] (act : G → X → X) (hm : Measurable (Function.uncurry act))
    (hmul : ∀ g g' x, act (g * g') x = act g (act g' x)) (hone : ∀ x, act 1 x = x)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Q : Measure X) [SFinite Q] (hQ : ∀ g, Q.map (act g) = Q) (x₀ : X)
    (htr : ∀ᵐ x ∂Q, ∃ g, act g x₀ = x) {f h : X → ℝ≥0∞} (hf : Measurable f) (hh : Measurable h) :
    (∫⁻ g, f (act g x₀) ∂μ) * ∫⁻ x, h x ∂Q = (∫⁻ x, f x ∂Q) * ∫⁻ g, h (act g⁻¹ x₀) ∂μ := by
  have hmg : ∀ g, Measurable (act g) := fun g => hm.comp measurable_prodMk_left
  have hm1 : Measurable fun p : X × G => act p.2 p.1 := hm.comp measurable_swap
  have hm2 : Measurable fun p : G × X => act p.1⁻¹ p.2 :=
    hm.comp (measurable_fst.inv.prodMk measurable_snd)
  calc (∫⁻ g, f (act g x₀) ∂μ) * ∫⁻ x, h x ∂Q
      = ∫⁻ x, (∫⁻ g, f (act g x₀) ∂μ) * h x ∂Q := (lintegral_const_mul _ hh).symm
    _ = ∫⁻ x, ∫⁻ g, f (act g x) * h x ∂μ ∂Q := by
        refine lintegral_congr_ae (htr.mono ?_)
        rintro x ⟨p, rfl⟩
        have hmx : Measurable fun g => f (act g (act p x₀)) := hf.comp (hm.comp measurable_prodMk_right)
        simp only
        rw [lintegral_mul_const _ hmx]
        congr 1
        simp_rw [← hmul]
        exact (lintegral_mul_right_eq_self (fun g => f (act g x₀)) p).symm
    _ = ∫⁻ g, ∫⁻ x, f (act g x) * h x ∂Q ∂μ :=
        lintegral_lintegral_swap ((hf.comp hm1).mul (hh.comp measurable_fst)).aemeasurable
    _ = ∫⁻ g, ∫⁻ x, f x * h (act g⁻¹ x) ∂Q ∂μ := by
        refine lintegral_congr fun g => ?_
        conv_rhs => rw [← hQ g]
        rw [lintegral_map (f := fun x => f x * h (act g⁻¹ x)) (hf.mul (hh.comp (hmg g⁻¹))) (hmg g)]
        refine lintegral_congr fun x => ?_
        rw [← hmul, inv_mul_cancel, hone]
    _ = ∫⁻ x, ∫⁻ g, f x * h (act g⁻¹ x) ∂μ ∂Q :=
        lintegral_lintegral_swap ((hf.comp measurable_snd).mul (hh.comp hm2)).aemeasurable
    _ = ∫⁻ x, f x * ∫⁻ g, h (act g⁻¹ x₀) ∂μ ∂Q := by
        refine lintegral_congr_ae (htr.mono ?_)
        rintro x ⟨p, rfl⟩
        have hmx : Measurable fun g : G => h (act g⁻¹ (act p x₀)) :=
          hh.comp (hm2.comp measurable_prodMk_right)
        simp only
        rw [lintegral_const_mul _ hmx]
        congr 1
        rw [← lintegral_mul_left_eq_self (fun g : G => h (act g⁻¹ x₀)) p⁻¹]
        refine lintegral_congr fun g => ?_
        rw [← hmul, _root_.mul_inv_rev, inv_inv]
    _ = _ := lintegral_mul_const _ hf

variable {k r : ℕ}

def act (g : Gp k r) (p : (Fin k → ℂ) × ℂ) : (Fin k → ℂ) × ℂ := opAct k r (Matrix.of (inc g)) p

theorem opVec_wI (p : (Fin k → ℂ) × ℂ) (m : Fin (k + 1)) : opVec k r p (wI k r m) = toW k p m := by
  have := m.isLt
  unfold opVec toW wI
  by_cases h : m.val < k
  · rw [dif_pos (by simp only; omega), dif_pos h]
    exact congrArg p.1 (Fin.ext (by simp))
  · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]

theorem opVec_inWb (p : (Fin k → ℂ) × ℂ) : inWb k r (opVec k r p) := by
  intro i hi
  unfold opVec
  rw [dif_neg (by omega), if_neg (by omega)]

theorem opCo_opVec (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by
  refine Eq.trans ?_ (ofW_toW p)
  unfold opCo ofW
  simp only [opVec_wI]

theorem continuous_opVec : Continuous (opVec k r) := by
  refine continuous_pi fun i => ?_
  unfold opVec
  split_ifs
  · exact (continuous_apply _).comp continuous_fst
  · exact continuous_snd
  · exact continuous_const

theorem continuous_act : Continuous (Function.uncurry (act (k := k) (r := r))) := by
  have hc : Continuous fun q : Gp k r × ((Fin k → ℂ) × ℂ) =>
      (Matrix.of (inc q.1) : Mat k r) *ᵥ opVec k r q.2 :=
    Continuous.matrix_mulVec (inc_cont.comp continuous_fst) (continuous_opVec.comp continuous_snd)
  exact (continuous_pi fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp hc).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp hc)

theorem act_mul (g g' : Gp k r) (p : (Fin k → ℂ) × ℂ) : act (g * g') p = act g (act g' p) := by
  unfold act
  have e : (Matrix.of (inc (g * g')) : Mat k r) = Matrix.of (inc g) * Matrix.of (inc g') := rfl
  rw [e, op_uwb_eq_emb (inc_mem g), op_uwb_eq_emb (inc_mem g'), ← emb_mul, opAct_emb, opAct_emb, opAct_emb,
    blkAct_mul]

theorem act_one (p : (Fin k → ℂ) × ℂ) : act (1 : Gp k r) p = p := by
  have e : (Matrix.of (inc (1 : Gp k r)) : Mat k r) = 1 := rfl
  unfold act opAct
  rw [e, Matrix.one_mulVec, opCo_opVec]

def pt (k : ℕ) (T' : ℝ) : (Fin k → ℂ) × ℂ := (0, (Real.sqrt T' : ℂ))

theorem opVec_pt (T' : ℝ) : opVec k r (pt k T') = opBase k r T' := by
  funext i
  unfold opVec pt opBase wLast
  simp only [Pi.smul_apply, bvec_apply, wI, Fin.ext_iff, Fin.val_last, smul_eq_mul, Pi.zero_apply]
  split_ifs <;> first | omega | simp

theorem act_pt (T' : ℝ) (g : Gp k r) : act g (pt k T') = opOrb k r T' (inc g) := by
  unfold act opAct opOrb
  rw [opVec_pt]

theorem act_trans {T' : ℝ} (hT : 0 < T') {x : (Fin k → ℂ) × ℂ} (hx : x ∈ hypS k T') :
    ∃ g : Gp k r, act g (pt k T') = x := by
  have hTz : Tz k r (opVec k r x) = T' := by
    unfold Tz
    rw [herm_wb _ _ (opVec_inWb x)]
    have e : wbPart k r (opVec k r x) = toW k x := funext fun m => opVec_wI x m
    rw [e]
    unfold herm
    rw [← qf_eq, Complex.ofReal_re, (hypS_iff T' x).1 hx, neg_neg]
  obtain ⟨p, hp, hpz⟩ := transW k r (opVec k r x) (opVec_inWb x) (hTz ▸ hT)
  rw [hTz] at hpz
  refine ⟨⟨p, hp⟩, (act_pt T' _).trans ?_⟩
  show opCo k r (p *ᵥ ((Real.sqrt T' : ℂ) • wLast k r)) = x
  rw [hpz, opCo_opVec]

theorem entry_bound {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) (i j : Fin (k + 1)) :
    Complex.normSq (μ i j) ≤ 1 + Complex.normSq (μ (Fin.last k) (Fin.last k)) := by
  have col : ∀ {ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}, νᴴ * Hb k * ν = Hb k → ∀ j,
      ∑ l : Fin k, Complex.normSq (ν l.castSucc j) - Complex.normSq (ν (Fin.last k) j) =
        if j = Fin.last k then -1 else 1 := by
    intro ν hν j
    have h := form_apply ν j j
    rw [hν] at h
    simp only [Hb, Matrix.diagonal_apply_eq, ← Complex.normSq_eq_conj_mul_self] at h
    apply Complex.ofReal_injective
    push_cast
    rw [← h]
    split_ifs <;> simp
  have hsq : Hb k * Hb k = 1 := by
    rw [Hb, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext j; split_ifs <;> norm_num
  have hμ' : (μᴴ)ᴴ * Hb k * μᴴ = Hb k := by
    have h1 : μ * (Hb k * μᴴ * Hb k) = 1 := mul_eq_one_comm.1 (hb_inv_mul hμ)
    rw [conjTranspose_conjTranspose]
    calc μ * Hb k * μᴴ = μ * (Hb k * μᴴ * Hb k) * Hb k := by
          simp only [Matrix.mul_assoc]; rw [hsq, Matrix.mul_one]
      _ = Hb k := by rw [h1, Matrix.one_mul]
  have row : ∀ j, Complex.normSq (μ (Fin.last k) j) ≤ Complex.normSq (μ (Fin.last k) (Fin.last k)) := by
    intro j
    refine Fin.lastCases le_rfl (fun j => ?_) j
    have h := col hμ' (Fin.last k)
    simp only [conjTranspose_apply, if_true, Complex.star_def, Complex.normSq_conj] at h
    have := Finset.single_le_sum (f := fun l : Fin k => Complex.normSq (μ (Fin.last k) l.castSucc))
      (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    linarith
  refine Fin.lastCases (by linarith [row j]) (fun i => ?_) i
  have h := col hμ j
  have := Finset.single_le_sum (f := fun l : Fin k => Complex.normSq (μ l.castSucc j))
    (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have h2 := row j
  split_ifs at h <;> linarith

theorem inc_closedEmbedding : IsClosedEmbedding (inc : Gp k r → Mt k r) :=
  amb_closed.isClosedEmbedding_subtypeVal

theorem orbit_proper {T' : ℝ} (hT : 0 < T') (R : ℝ) :
    ∃ K : Set (Gp k r), IsCompact K ∧ ∀ g, act g (pt k T') ∈ Metric.closedBall 0 R → g ∈ K := by
  refine ⟨inc ⁻¹' Metric.closedBall 0 (Real.sqrt (1 + R ^ 2 / T')),
    inc_closedEmbedding.isCompact_preimage (isCompact_closedBall _ _), fun g hg => ?_⟩
  set μ := (Matrix.of (inc g) : Mat k r).submatrix (wI k r) (wI k r) with hμdef
  have he : (Matrix.of (inc g) : Mat k r) = embWb k r μ := op_uwb_eq_emb (inc_mem g)
  have hμ : μᴴ * Hb k * μ = Hb k := by
    rw [← emb_mem (r := r), ← he]; exact (inc_mem g).1
  have hlast : Complex.normSq (μ (Fin.last k) (Fin.last k)) ≤ R ^ 2 / T' := by
    rw [mem_closedBall_zero_iff] at hg
    have h2 : ‖(act g (pt k T')).2‖ ≤ R := (norm_snd_le _).trans hg
    have e : (act g (pt k T')).2 = (Real.sqrt T' : ℂ) * μ (Fin.last k) (Fin.last k) := by
      rw [act_pt]
      show ((Matrix.of (inc g) : Mat k r) *ᵥ ((Real.sqrt T' : ℂ) • bvec (wI k r (Fin.last k))))
        (wI k r (Fin.last k)) = _
      rw [Matrix.mulVec_smul, Pi.smul_apply, mulVec_bvec]
      rfl
    have h3 : Complex.normSq (act g (pt k T')).2 ≤ R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [e, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hT.le] at h3
    rw [le_div_iff₀ hT]
    linarith
  have hpos : 0 ≤ R ^ 2 / T' := by positivity
  have hent : ∀ i j, Complex.normSq (inc g i j) ≤ 1 + R ^ 2 / T' := by
    intro i j
    have e : inc g i j = embWb k r μ i j := congrFun (congrFun he i) j
    rw [e]
    by_cases hi : mid k r i
    · by_cases hj : mid k r j
      · rw [emb_mid _ i j hi hj]
        linarith [entry_bound hμ (midx hi) (midx hj)]
      · rw [emb_out_col _ i j hj]
        split_ifs <;> simp <;> linarith
    · rw [emb_out_row _ i j hi]
      split_ifs <;> simp <;> linarith
  show inc g ∈ Metric.closedBall 0 _
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro j
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  exact hent i j

theorem pull_right (ν : Measure (Mt k r)) (hc : ν {x | Matrix.of x ∉ UWb k r} = 0)
    (h : ∀ p ∈ UWb k r, ν.map (rmulM p) = ν) : (pull ν).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  apply inc_memb.map_injective
  have e : (inc : Gp k r → Mt k r) ∘ (fun x => x * g) = rmulM (Matrix.of (inc g)) ∘ inc := rfl
  show ((pull ν).map (fun x => x * g)).map inc = (pull ν).map inc
  rw [Measure.map_map inc_memb.measurable (continuous_mul_const g).measurable, e,
    ← Measure.map_map (rmulM_cont _).measurable inc_memb.measurable, map_pull ν hc, h _ (inc_mem g)]

theorem pull_compact (ν : Measure (Mt k r)) (hG : IsGaugeOn k r (UWb k r) ν) {K : Set (Gp k r)}
    (hK : IsCompact K) : pull ν K ≠ ⊤ := by
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  obtain ⟨⟨hσ, hne, hc, hl⟩, -⟩ := hG
  haveI : LocallyCompactSpace (Gp k r) := inc_closedEmbedding.locallyCompactSpace
  haveI : T2Space (Gp k r) := inc_closedEmbedding.isEmbedding.t2Space
  haveI := pull_sigmaFinite ν
  haveI := pull_left ν hl
  have key := measure_eq_div_smul (Measure.haar : Measure (Gp k r)) (pull ν) (s := inc ⁻¹' bBall k r ρ)
    (by rw [pull_apply ν hc]; exact h0.ne') (by rw [pull_apply ν hc]; exact ht.ne)
  set c := (Measure.haar : Measure (Gp k r)) (inc ⁻¹' bBall k r ρ) / pull ν (inc ⁻¹' bBall k r ρ)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at key
    exact NeZero.ne _ key
  have h1 : (Measure.haar : Measure (Gp k r)) K ≠ ⊤ := hK.measure_lt_top.ne
  rw [key, Measure.smul_apply, smul_eq_mul] at h1
  intro htop
  rw [htop, ENNReal.mul_top hc0] at h1
  exact h1 rfl

theorem orbRepY : OrbRepY := by
  intro k r T' hk hT νg hG Q hQ hS hC
  by_cases hQ0 : Q = 0
  · exact ⟨0, ENNReal.zero_ne_top, by rw [hQ0, zero_smul]⟩
  haveI : IsFiniteMeasureOnCompacts Q := ⟨fun C h => hC C h⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, Q (Metric.closedBall 0 R) ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ0
    rw [← Measure.measure_univ_eq_zero, ← Metric.iUnion_closedBall_nat (0 : (Fin k → ℂ) × ℂ)]
    exact measure_iUnion_null h
  set C : Set ((Fin k → ℂ) × ℂ) := Metric.closedBall 0 R with hCdef
  have hCm : MeasurableSet C := Metric.isClosed_closedBall.measurableSet
  have hRt : Q C ≠ ⊤ := (hC C (isCompact_closedBall _ _)).ne
  have hU := unimodW k r νg hk hG
  have hfin := fun K => pull_compact νg hG (K := K)
  obtain ⟨⟨hσ, hne, hc, hl⟩, -⟩ := hG
  haveI := pull_sigmaFinite νg
  haveI := pull_left νg hl
  haveI := pull_right νg hc hU
  have hom := (continuous_opOrb (k := k) (r := r) T').measurable
  have htr : ∀ᵐ x ∂Q, ∃ g : Gp k r, act g (pt k T') = x := by
    have : ∀ᵐ x ∂Q, x ∈ hypS k T' := hS
    exact this.mono fun x hx => act_trans hT hx
  set b := ∫⁻ g : Gp k r, C.indicator 1 (act g⁻¹ (pt k T')) ∂(pull νg) with hb
  have key : ∀ E, MeasurableSet E → νg.map (opOrb k r T') E * Q C = Q E * b := by
    intro E hE
    have h := fubini_identity act continuous_act.measurable act_mul act_one (pull νg) Q
      (fun g => hQ _ (inc_mem g)) (pt k T') htr (measurable_one.indicator hE) (measurable_one.indicator hCm)
    rw [lintegral_indicator_one hE, lintegral_indicator_one hCm] at h
    rw [← h]
    congr 1
    rw [← lintegral_indicator_one hE, ← map_pull νg hc, lintegral_map (measurable_one.indicator hE) hom,
      inc_memb.lintegral_map, map_pull νg hc]
    simp_rw [act_pt]
  have hbt : b ≠ ⊤ := by
    obtain ⟨K, hK, hKm⟩ := orbit_proper (k := k) (r := r) hT R
    haveI : T2Space (Gp k r) := inc_closedEmbedding.isEmbedding.t2Space
    refine ne_top_of_le_ne_top (hfin K⁻¹ hK.inv) ?_
    rw [← lintegral_indicator_one hK.inv.measurableSet]
    refine lintegral_mono fun g => ?_
    by_cases hg : act g⁻¹ (pt k T') ∈ C
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (Set.mem_inv.2 (hKm _ hg))]
      rfl
    · rw [Set.indicator_of_notMem hg]; exact zero_le
  have hb0 : b ≠ 0 := by
    intro h0
    have h := key Set.univ MeasurableSet.univ
    rw [h0, mul_zero, Measure.map_apply hom MeasurableSet.univ, Set.preimage_univ] at h
    rcases mul_eq_zero.1 h with h | h
    · exact hne (Measure.measure_univ_eq_zero.1 h)
    · exact hR h
  refine ⟨Q C / b, (ENNReal.div_lt_top hRt hb0).ne, ?_⟩
  ext E hE
  rw [Measure.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_right_comm, mul_comm (Q C), key E hE, mul_assoc,
    ENNReal.mul_inv_cancel hb0 hbt, mul_one]

end GlobalTheory.HypOrbitUnique
