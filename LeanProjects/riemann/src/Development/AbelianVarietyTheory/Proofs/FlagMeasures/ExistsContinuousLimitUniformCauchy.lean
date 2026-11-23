import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.RegLimit

theorem sq_le_four (a e b : ENNReal) (h : a ≤ e + b) : a ^ 2 ≤ 4 * (e ^ 2 + b ^ 2) := by
  have h1 : e + b ≤ 2 * max e b := by
    rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have h2 : max e b ^ 2 ≤ e ^ 2 + b ^ 2 := by
    rcases le_total e b with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_self_add
  calc a ^ 2 ≤ (2 * max e b) ^ 2 := pow_le_pow_left₀ zero_le (h.trans h1) 2
    _ = 4 * max e b ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (e ^ 2 + b ^ 2) := by gcongr

theorem exists_continuous_limit : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] (f : ℕ → Mat k r → Wp) (g : Mt k r → Wp), (∀ j, ContinuousOn (f j) (GG k r)) → (∀ Q : Set (Mt k r), IsCompact Q → AEStronglyMeasurable g (μ.restrict Q)) → (∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q, Matrix.of x ∈ GG k r → ‖f j (Matrix.of x) - f l (Matrix.of x)‖ ≤ ε) → (∀ Q : Set (Mt k r), IsCompact Q → Filter.Tendsto (fun j : ℕ => ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0)) → ∃ F : Mat k r → Wp, ContinuousOn F (GG k r) ∧ ((fun x : Mt k r => F (Matrix.of x)) =ᵐ[μ] g) ∧ ∀ x ∈ GG k r, Filter.Tendsto (fun j : ℕ => f j x) Filter.atTop (nhds (F x)) := by
  intro k r μ hμ Wp _ _ _ f g hf hg hC hL
  set T : Set (Mt k r) → Set (Mat k r) := fun Q => GG k r ∩ {y | Matrix.of.symm y ∈ Q} with hT
  have hUC : ∀ Q : Set (Mt k r), IsCompact Q → UniformCauchySeqOn f Filter.atTop (T Q) := by
    intro Q hQ
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hC Q hQ (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    have := hN m hm n hn (Matrix.of.symm y) hy.2 (by simpa using hy.1)
    simp only [Equiv.apply_symm_apply] at this
    rw [dist_eq_norm]; linarith
  set F : Mat k r → Wp := fun y => Filter.limUnder Filter.atTop (fun j => f j y) with hFdef
  have hF : ∀ y ∈ GG k r, Filter.Tendsto (fun j => f j y) Filter.atTop (nhds (F y)) := by
    intro y hy
    have hc := (hUC {Matrix.of.symm y} isCompact_singleton).cauchySeq
      (show y ∈ T {Matrix.of.symm y} from ⟨hy, rfl⟩)
    obtain ⟨L, hL'⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨L, hL'⟩
  have hU : ∀ Q : Set (Mt k r), IsCompact Q → TendstoUniformlyOn f F Filter.atTop (T Q) :=
    fun Q hQ => (hUC Q hQ).tendstoUniformlyOn_of_tendsto (fun y hy => hF y hy.1)
  have hsymm : Continuous (fun y : Mat k r => (Matrix.of.symm y : Mt k r)) := continuous_id
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hFc : ContinuousOn F (GG k r) := by
    intro x hx
    set Q : Set (Mt k r) := Metric.closedBall (Matrix.of.symm x) 1
    have hQ : IsCompact Q := isCompact_closedBall _ _
    have h1 : ContinuousOn F (T Q) :=
      (hU Q hQ).continuousOn (Filter.Eventually.of_forall (f := Filter.atTop) fun j => (hf j).mono Set.inter_subset_left).frequently
    have hxT : x ∈ T Q := ⟨hx, show (Matrix.of.symm x : Mt k r) ∈ Q from Metric.mem_closedBall_self (x := (Matrix.of.symm x : Mt k r)) zero_le_one⟩
    refine (h1 x hxT).mono_of_mem_nhdsWithin ?_
    exact inter_mem_nhdsWithin _ (hsymm.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ zero_lt_one))

  have hGcl : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := (gg_closedSub k r).2.1.preimage hof
  have hGae : ∀ᵐ x ∂μ, Matrix.of x ∈ GG k r := ae_iff.2 hμ.2.2.1
  have hFm : AEStronglyMeasurable (fun x : Mt k r => F (Matrix.of x)) μ := by
    have h1 : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} :=
      hFc.comp hof.continuousOn (fun x hx => hx)
    have h2 := h1.aestronglyMeasurable (μ := μ) hGcl.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) hGae] at h2
  have hQae : ∀ Q : Set (Mt k r), IsCompact Q → MeasurableSet Q →
      ∀ᵐ x ∂(μ.restrict Q), F (Matrix.of x) = g x := by
    intro Q hQ hQm
    have hQfin : μ Q ≠ ⊤ := (haar_compact_lt_top hμ hQ).ne
    set a : Mt k r → ENNReal := fun x => (‖F (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 with ha
    have hbound : ∀ n : ℕ, ∫⁻ x in Q, a x ∂μ ≤
        4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q + ENNReal.ofReal (1 / ((n : ℝ) + 1))) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have e1 := Metric.tendstoUniformlyOn_iff.1 (hU Q hQ) _ hpos
      have e2 := ENNReal.tendsto_nhds_zero.1 (hL Q hQ) _ (ENNReal.ofReal_pos.2 hpos)
      obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
      calc ∫⁻ x in Q, a x ∂μ
          ≤ ∫⁻ x in Q, 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 +
              (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem hQm, ae_restrict_of_ae hGae] with x hxQ hxG
            apply sq_le_four
            have hd := hj1 (Matrix.of x) ⟨hxG, by simpa using hxQ⟩
            have htri : ‖F (Matrix.of x) - g x‖₊ ≤
                ‖F (Matrix.of x) - f j (Matrix.of x)‖₊ + ‖f j (Matrix.of x) - g x‖₊ := by
              have : F (Matrix.of x) - g x = (F (Matrix.of x) - f j (Matrix.of x)) + (f j (Matrix.of x) - g x) := by
                abel
              rw [this]; exact nnnorm_add_le _ _
            calc (‖F (Matrix.of x) - g x‖₊ : ENNReal)
                ≤ (‖F (Matrix.of x) - f j (Matrix.of x)‖₊ : ENNReal) + ‖f j (Matrix.of x) - g x‖₊ := by
                  rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.2 htri
              _ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ‖f j (Matrix.of x) - g x‖₊ := by
                  gcongr
                  exact ENNReal.coe_le_coe.2 ((Real.le_toNNReal_iff_coe_le hpos.le).2
                    (by rw [coe_nnnorm, ← dist_eq_norm]; exact hd.le))
        _ = 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q +
              ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) := by
            rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left measurable_const,
              lintegral_const, Measure.restrict_apply_univ]
        _ ≤ _ := by gcongr
    have ht : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    have ht2 : Filter.Tendsto (fun n : ℕ => 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)))) Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul ((ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) ht)
        (Or.inr hQfin)).add ht) (a := (4 : ENNReal)) (Or.inr (by norm_num))
      simpa using this
    have hzero : ∫⁻ x in Q, a x ∂μ = 0 := le_antisymm (ge_of_tendsto' ht2 hbound) (zero_le)
    have hm : AEStronglyMeasurable (fun x => F (Matrix.of x) - g x) (μ.restrict Q) :=
      hFm.restrict.sub (hg Q hQ)
    have hae := (lintegral_eq_zero_iff' (hm.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)).1 hzero
    filter_upwards [hae] with x hx
    simpa [ha, sub_eq_zero] using hx
  refine ⟨F, hFc, ?_, hF⟩
  have hall : ∀ n : ℕ, ∀ᵐ x ∂(μ.restrict (Metric.closedBall (0 : Mt k r) n)), F (Matrix.of x) = g x :=
    fun n => hQae _ (isCompact_closedBall _ _) Metric.isClosed_closedBall.measurableSet
  have := (ae_restrict_iUnion_iff _ _).2 hall
  rwa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] at this

end GlobalTheory.SgInf.RegLimit
