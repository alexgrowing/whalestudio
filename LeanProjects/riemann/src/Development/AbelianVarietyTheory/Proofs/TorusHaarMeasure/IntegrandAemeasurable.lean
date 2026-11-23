import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ContDiff ENNReal

namespace GlobalTheory.SkodaIter

noncomputable section

variable {n : ℕ} {U : Set (V n)}

def integrand (s : Fin n → V n → ℂ) (ph : V n → ℝ) (t : ℝ) (G : V n → ℂ) (z : V n) : ℝ≥0∞ :=
  ENNReal.ofReal (‖G z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z))

theorem holo_val {f : V n → ℂ} (hf : DifferentiableOn ℂ f U) :
    Holo n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  exact (hf.mono (HE.target_sub he)).congr (HE.comp_symm_eqOn f he)

theorem normSq_continuousOn {s : Fin n → V n → ℂ} (hs : ∀ k, DifferentiableOn ℂ (s k) U) :
    ContinuousOn (fun z => ∑ k, ‖s k z‖ ^ 2) U := by
  exact continuousOn_finset_sum _ (fun k _ => ((hs k).continuousOn.norm).pow 2)

theorem normSq_pos {s : Fin n → V n → ℂ} {z : V n} {k : Fin n} (h : s k z ≠ 0) :
    0 < ∑ k, ‖s k z‖ ^ 2 := by
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) 2)
    (Finset.single_le_sum (f := fun j => ‖s j z‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k))

theorem integrand_aemeasurable (hU : IsOpen U) {s : Fin n → V n → ℂ}
    (hs : ∀ k, DifferentiableOn ℂ (s k) U) {ph : V n → ℝ} (hph : ContinuousOn ph U) (t : ℝ)
    {G : V n → ℂ} (hG : DifferentiableOn ℂ G U) :
    AEMeasurable (integrand s ph t G) (volume.restrict U) := by
  have hUm := hU.measurableSet
  have h1 : AEMeasurable (fun z => ‖G z‖ ^ 2) (volume.restrict U) :=
    (hG.continuousOn.norm.pow 2).aemeasurable hUm
  have h2 : AEMeasurable (fun z => ∑ k, ‖s k z‖ ^ 2) (volume.restrict U) :=
    (normSq_continuousOn hs).aemeasurable hUm
  have h3 : AEMeasurable (fun z => Real.exp (-ph z)) (volume.restrict U) :=
    (Real.continuous_exp.comp_continuousOn hph.neg).aemeasurable hUm
  exact ENNReal.measurable_ofReal.comp_aemeasurable ((h1.mul (h2.pow_const (-t))).mul h3)

theorem integrand_add_le (s : Fin n → V n → ℂ) (ph : V n → ℝ) (t : ℝ) (G G' : V n → ℂ) (z : V n) :
    integrand s ph t (fun y => G y + G' y) z ≤
      2 * integrand s ph t G z + 2 * integrand s ph t G' z := by
  simp only [integrand]
  have hA : 0 ≤ (∑ k, ‖s k z‖ ^ 2) ^ (-t) := Real.rpow_nonneg (by positivity) _
  have hE : 0 < Real.exp (-ph z) := Real.exp_pos _
  have hAE : 0 ≤ (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z) := mul_nonneg hA hE.le
  have hn : ‖G z + G' z‖ ^ 2 ≤ 2 * ‖G z‖ ^ 2 + 2 * ‖G' z‖ ^ 2 := by
    have := norm_add_le (G z) (G' z)
    nlinarith [norm_nonneg (G z), norm_nonneg (G' z), norm_nonneg (G z + G' z), sq_nonneg (‖G z‖ - ‖G' z‖)]
  have ha : 0 ≤ ‖G z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z) := by
    rw [mul_assoc]; exact mul_nonneg (sq_nonneg _) hAE
  have hb : 0 ≤ ‖G' z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z) := by
    rw [mul_assoc]; exact mul_nonneg (sq_nonneg _) hAE
  calc ENNReal.ofReal (‖G z + G' z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z))
      ≤ ENNReal.ofReal (2 * (‖G z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z)) +
          2 * (‖G' z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z))) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_right hn hAE]
    _ = ENNReal.ofReal (2 * (‖G z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z))) +
          ENNReal.ofReal (2 * (‖G' z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z))) :=
        ENNReal.ofReal_add (mul_nonneg zero_le_two ha) (mul_nonneg zero_le_two hb)
    _ = 2 * ENNReal.ofReal (‖G z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z)) +
          2 * ENNReal.ofReal (‖G' z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z)) := by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_mul zero_le_two]
        simp

theorem good_sum (hU : IsOpen U) {s : Fin n → V n → ℂ}
    (hs : ∀ k, DifferentiableOn ℂ (s k) U) {ph : V n → ℝ} (hph : ContinuousOn ph U) (t : ℝ)
    {ι : Type*} (G : ι → V n → ℂ) (T : Finset ι)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U ∧ ∫⁻ z in U, integrand s ph t (G i) z < ⊤) :
    DifferentiableOn ℂ (fun y => ∑ i ∈ T, G i y) U ∧
      ∫⁻ z in U, integrand s ph t (fun y => ∑ i ∈ T, G i y) z < ⊤ := by
  classical
  refine Finset.induction_on T ?_ ?_
  · refine ⟨by simpa using (differentiableOn_const (c := (0:ℂ)) (s := U)), ?_⟩
    simp [integrand]
  · intro i T hi ih
    obtain ⟨hd, hint⟩ := ih
    have hdi := (hG i).1
    have hfin := (hG i).2
    simp only [Finset.sum_insert hi]
    refine ⟨hdi.add hd, ?_⟩
    calc ∫⁻ z in U, integrand s ph t (fun y => G i y + ∑ j ∈ T, G j y) z
        ≤ ∫⁻ z in U, (2 * integrand s ph t (G i) z + 2 * integrand s ph t (fun y => ∑ j ∈ T, G j y) z) :=
          lintegral_mono (fun z => integrand_add_le s ph t _ _ z)
      _ = 2 * (∫⁻ z in U, integrand s ph t (G i) z) + 2 * (∫⁻ z in U, integrand s ph t (fun y => ∑ j ∈ T, G j y) z) := by
          rw [lintegral_add_left' ((integrand_aemeasurable hU hs hph t hdi).const_mul 2),
            lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
      _ < ⊤ := by
          apply ENNReal.add_lt_top.2
          constructor <;> apply ENNReal.mul_lt_top <;> first | assumption | simp

theorem extend (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    {ph : V n → ℝ} (hph : ContinuousOn ph U) {t : ℝ} (ht : 0 ≤ t) {G : V n → ℂ}
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ s k0 y ≠ 0})
    (hI : ∫⁻ z in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G z < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ s k0 y ≠ 0} ∧
      ∫⁻ z in U, integrand s ph t G' z < ⊤ := by
  have hM : IsOpen {y | y ∈ U ∧ s k0 y ≠ 0} := HE.isOpen_punct hU (hs k0)
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤ := by
    intro p hp
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
    have hKU : closedBall p (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hbU : ball p (ε / 2) ⊆ U := ball_subset_closedBall.trans hKU
    have hK : IsCompact (closedBall p (ε / 2)) := isCompact_closedBall p _
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((normSq_continuousOn hs).mono hKU)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hph.mono hKU)
    refine ⟨ε / 2, half_pos hε, hbU, ?_⟩
    have hAM : ball p (ε / 2) \ {y | s k0 y = 0} ⊆ {y | y ∈ U ∧ s k0 y ≠ 0} :=
      fun y hy => ⟨hbU hy.1, hy.2⟩
    have hAeq : ball p (ε / 2) \ {y | s k0 y = 0} = ball p (ε / 2) ∩ {y | y ∈ U ∧ s k0 y ≠ 0} := by
      ext y
      exact ⟨fun h => ⟨h.1, hbU h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    have hAm : MeasurableSet (ball p (ε / 2) \ {y | s k0 y = 0}) := by
      rw [hAeq]; exact (isOpen_ball.inter hM).measurableSet
    have hpt : ∀ y ∈ ball p (ε / 2) \ {y | s k0 y = 0},
        ENNReal.ofReal (‖G y‖ ^ 2) ≤ ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y := by
      intro y hy
      have hyK : y ∈ closedBall p (ε / 2) := ball_subset_closedBall hy.1
      have hpos : 0 < ∑ k, ‖s k y‖ ^ 2 := normSq_pos (k := k0) hy.2
      have hfB : ∑ k, ‖s k y‖ ^ 2 ≤ B := (Real.le_norm_self _).trans (hB y hyK)
      have hB0 : 0 < B := hpos.trans_le hfB
      have hphC : ph y ≤ C := (Real.le_norm_self _).trans (hC y hyK)
      have h1 : 1 ≤ (∑ k, ‖s k y‖ ^ 2) ^ (-t) * B ^ t := by
        rw [Real.rpow_neg hpos.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hpos t)]
        exact Real.rpow_le_rpow hpos.le hfB ht
      have h2 : 1 ≤ Real.exp C * Real.exp (-ph y) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      have h3 := mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
      simp only [integrand]
      rw [← ENNReal.ofReal_mul (mul_pos (Real.rpow_pos_of_pos hB0 t) (Real.exp_pos C)).le]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖G y‖)]
    calc ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2)
        ≤ ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0},
            ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y :=
          lintegral_mono_ae (ae_restrict_of_forall_mem hAm hpt)
      _ = ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, integrand s ph t G y :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G y :=
          mul_le_mul (le_refl _) (lintegral_mono_set hAM) zero_le zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI
  obtain ⟨G', hG'd, hG'eq⟩ := HE.ext_glue hU (s k0) G (hs k0) hgn hG hloc
  refine ⟨G', hG'd, hG'eq, ?_⟩
  have hnull : volume {y | y ∈ U ∧ s k0 y = 0} = 0 := HE.zeros_null hU (hs k0) hgn
  have hae : (U : Set (V n)) =ᵐ[volume] {y | y ∈ U ∧ s k0 y ≠ 0} := by
    have e1 : volume (U \ {y | y ∈ U ∧ s k0 y ≠ 0}) = 0 :=
      measure_mono_null (fun y (hy : y ∈ U \ {y | y ∈ U ∧ s k0 y ≠ 0}) =>
        (⟨hy.1, Classical.byContradiction fun h => hy.2 ⟨hy.1, h⟩⟩ : y ∈ {y | y ∈ U ∧ s k0 y = 0})) hnull
    have e2 : volume ({y | y ∈ U ∧ s k0 y ≠ 0} \ U) = 0 :=
      measure_mono_null (fun y hy => (hy.2 hy.1.1).elim) measure_empty
    exact (ae_eq_set (μ := volume)).2 ⟨e1, e2⟩
  rw [Measure.restrict_congr_set hae]
  rw [lintegral_congr_ae (ae_restrict_of_forall_mem hM.measurableSet
    (fun y hy => show integrand s ph t G' y = integrand s ph t G y by simp only [integrand, hG'eq hy]))]
  exact hI

theorem step (hn : 2 ≤ n) (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    (hS : ∃ S : EtaleStein n {z | z ∈ U ∧ s k0 z ≠ 0}, S.z = Subtype.val)
    {ph : V n → ℝ} (hph : ContDiffOn ℝ ∞ ph U)
    (hl : ∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => ((ph w : ℝ) : ℂ)) z ξ).re)
    {t : ℝ} (ht : (n : ℝ) - 1 < t) {F : V n → ℂ} (hF : DifferentiableOn ℂ F U)
    (hI : ∫⁻ z in U, integrand s ph (t + 1) F z < ⊤) :
    ∃ h : Fin n → V n → ℂ, (∀ i, DifferentiableOn ℂ (h i) U ∧
      ∫⁻ z in U, integrand s ph t (h i) z < ⊤) ∧ ∀ z ∈ U, F z = ∑ i, s i z * h i z := by
  obtain ⟨S, hSz⟩ := hS
  have hM : IsOpen {z | z ∈ U ∧ s k0 z ≠ 0} := HE.isOpen_punct hU (hs k0)
  have ht0 : 0 ≤ t := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hint : ∫⁻ x, ENNReal.ofReal (‖F x.1‖ ^ 2 * (∑ i, ‖s i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph x.1))
      ∂(vol n S.z) < ⊤ := by
    rw [hSz]
    refine (HE.lintegral_val hM (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖s i y‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-ph y)))).trans_lt ?_
    exact lt_of_le_of_lt (lintegral_mono_set (fun y hy => hy.1)) hI
  obtain ⟨hh, hhh, hdec, hbound⟩ := ReciprocityTheory.L2DbarEstimates.skoda n _ S n (fun i x => s i x.1) (fun x => ph x.1) t
    (fun x => F x.1) hn
    (fun i => by rw [hSz]; exact holo_val ((hs i).mono (fun y hy => hy.1)))
    (fun x => ⟨k0, x.2.2⟩)
    (by rw [hSz]; exact HE.smoothR_val (hph.mono (fun y hy => hy.1)))
    (by rw [hSz]; intro x ξ; rw [HE.levi_val hM ph x ξ]; exact hl x.1 x.2.1 ξ)
    ht
    (by rw [hSz]; exact holo_val (hF.mono (fun y hy => hy.1)))
    hint
  have hfin := lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint)
  rw [hSz] at hfin
  have hhv : ∀ i, Holo n (Subtype.val : {z // z ∈ {z | z ∈ U ∧ s k0 z ≠ 0}} → V n) (hh i) := by
    intro i; rw [← hSz]; exact hhh i
  have hGd : ∀ i, DifferentiableOn ℂ (HE.ext0 (hh i)) {z | z ∈ U ∧ s k0 z ≠ 0} :=
    fun i => HE.differentiableOn_extendByZero hM (hhv i)
  have hGi : ∀ i, ∫⁻ y in {z | z ∈ U ∧ s k0 z ≠ 0}, integrand s ph t (HE.ext0 (hh i)) y < ⊤ := by
    intro i
    refine ((HE.lintegral_val hM (fun y => integrand s ph t (HE.ext0 (hh i)) y)).symm.trans_le ?_).trans_lt hfin
    refine lintegral_mono (fun x => ?_)
    simp only [integrand, HE.extendByZeroOnSubset_apply_coe]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun j => ‖hh j x‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
      (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le
  choose H hHd hHeq hHint using fun i => extend hU k0 hs hgn hph.continuousOn ht0 (hGd i) (hGi i)
  refine ⟨H, fun i => ⟨hHd i, hHint i⟩, ?_⟩
  have hDc : ContinuousOn (fun z => F z - ∑ i, s i z * H i z) U :=
    hF.continuousOn.sub (continuousOn_finset_sum _ (fun i _ => (hs i).continuousOn.mul (hHd i).continuousOn))
  intro z hz
  by_contra hne
  have hW := hDc.isOpen_inter_preimage hU (isOpen_compl_singleton (x := (0:ℂ)))
  obtain ⟨y, ⟨hyU, hyD⟩, hy0⟩ := hgn _ hW Set.inter_subset_left ⟨z, hz, by simpa [sub_eq_zero] using hne⟩
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hyD
  apply hyD
  have hd := hdec ⟨y, hyU, hy0⟩
  dsimp only at hd
  rw [sub_eq_zero, hd]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hHeq i ⟨hyU, hy0⟩]
  exact (congrArg (fun w => s i y * w) (HE.extendByZeroOnSubset_apply_coe (hh i) ⟨y, hyU, hy0⟩)).symm

private theorem mul_prod_pow_eq_prod_pow_add_single {n : ℕ} {X : Type*} (s : Fin n → X → ℂ) (z : X) (β : Fin n → ℕ)
    (i : Fin n) : s i z * ∏ k, s k z ^ β k = ∏ k, s k z ^ (β + (Pi.single i 1 : Fin n → ℕ)) k := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, pow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, pow_one]

private theorem sum_antidiagonal_tuple_add_single_eq_filter {n : ℕ} (m : ℕ) (i : Fin n) (f : (Fin n → ℕ) → ℂ) :
    ∑ β ∈ Finset.Nat.antidiagonalTuple n m, f (β + Pi.single i 1) =
      ∑ α ∈ (Finset.Nat.antidiagonalTuple n (m + 1)).filter (fun α => 0 < α i), f α := by
  have hle : ∀ α : Fin n → ℕ, 0 < α i → (Pi.single i 1 : Fin n → ℕ) ≤ α := by
    intro α hα j
    by_cases hj : j = i
    · rw [hj, Pi.single_eq_same]; exact hα
    · rw [Pi.single_eq_of_ne hj]; exact Nat.zero_le _
  have hsum : ∑ j, (Pi.single i 1 : Fin n → ℕ) j = 1 := by
    rw [Finset.sum_eq_single i (fun j _ hj => Pi.single_eq_of_ne hj 1)
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
  refine Finset.sum_nbij' (fun β => β + Pi.single i 1) (fun α => α - Pi.single i 1) ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hsum, hβ]
    · simp only [Pi.add_apply, Pi.single_eq_same]; omega
  · intro α hα
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
    have key : ∑ j, (α - (Pi.single i 1 : Fin n → ℕ)) j + ∑ j, (Pi.single i 1 : Fin n → ℕ) j = ∑ j, α j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [← Pi.add_apply, tsub_add_cancel_of_le (hle α hα.2)])
    omega
  · intro β _
    exact add_tsub_cancel_right β _
  · intro α hα
    simp only [Finset.mem_coe, Finset.mem_filter] at hα
    exact tsub_add_cancel_of_le (hle α hα.2)
  · intro β _
    rfl

theorem iterated_division : ∀ (n : ℕ), 2 ≤ n → ∀ (U : Set (V n)), IsOpen U → IsPreconnected U →
    ∀ (s : Fin n → V n → ℂ) (k0 : Fin n), (∀ k, DifferentiableOn ℂ (s k) U) → (∃ z ∈ U, s k0 z ≠ 0) →
    (∃ S : EtaleStein n {z | z ∈ U ∧ s k0 z ≠ 0}, S.z = Subtype.val) →
    ∀ ph0 : V n → ℝ, ContDiffOn ℝ ∞ ph0 U →
    (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => ((ph0 w : ℝ) : ℂ)) z ξ).re) →
    ∀ (a : ℕ) (F : V n → ℂ), DifferentiableOn ℂ F U →
    ∫⁻ z in U, ENNReal.ofReal (‖F z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-((a : ℝ) + n - 1 / 2)) * Real.exp (-ph0 z)) < ⊤ →
    ∃ H : (Fin n → ℕ) → V n → ℂ, (∀ α, DifferentiableOn ℂ (H α) U ∧
      ∫⁻ z in U, ENNReal.ofReal (‖H α z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) * Real.exp (-ph0 z)) < ⊤) ∧
      ∀ z ∈ U, F z = ∑ α ∈ Finset.Nat.antidiagonalTuple n a, (∏ k, s k z ^ α k) * H α z := by
  intro n hn U hU hUc s k0 hs hz hS ph0 hph hl a
  obtain ⟨z0, hz0U, hz0⟩ := hz
  have hgn := HE.hgn_of hU hUc (hs k0) hz0U (fun hev => hz0 (Filter.EventuallyEq.eq_of_nhds hev))
  induction a with
  | zero =>
    intro F hF hI
    have e : ((0:ℕ):ℝ) + n - 1 / 2 = (n:ℝ) - 1 / 2 := by simp
    rw [e] at hI
    refine ⟨fun _ => F, fun _ => ⟨hF, hI⟩, ?_⟩
    intro z _
    simp [Finset.Nat.antidiagonalTuple_zero_right]
  | succ m ih =>
    intro F hF hI
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    obtain ⟨h, hh, hdec⟩ := step (t := (m:ℝ) + n - 1 / 2) hn hU k0 hs hgn hS hph hl (by linarith) hF (by
      have e : (m:ℝ) + n - 1 / 2 + 1 = ((m + 1 : ℕ) : ℝ) + n - 1 / 2 := by push_cast; ring
      simp only [integrand]
      rw [e]
      exact hI)
    choose Hs hHs hHdec using fun i => ih (h i) (hh i).1 (hh i).2
    refine ⟨fun α z => ∑ i ∈ Finset.univ.filter (fun i => 0 < α i), Hs i (α - Pi.single i 1) z,
      fun α => good_sum hU hs hph.continuousOn ((n:ℝ) - 1 / 2) (fun i => Hs i (α - Pi.single i 1))
        (Finset.univ.filter (fun i => 0 < α i)) (fun i => hHs i _), ?_⟩
    intro z hz
    rw [hdec z hz]
    beta_reduce
    calc ∑ i, s i z * h i z
        = ∑ i, ∑ β ∈ Finset.Nat.antidiagonalTuple n m, (∏ k, s k z ^ (β + (Pi.single i 1 : Fin n → ℕ)) k) * Hs i β z := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hHdec i z hz, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun β _ => ?_)
          rw [← mul_assoc, mul_prod_pow_eq_prod_pow_add_single]
      _ = ∑ i, ∑ α ∈ (Finset.Nat.antidiagonalTuple n (m + 1)).filter (fun α => 0 < α i),
            (∏ k, s k z ^ α k) * Hs i (α - Pi.single i 1) z := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Eq.trans ?_ (sum_antidiagonal_tuple_add_single_eq_filter m i _)
          refine Finset.sum_congr rfl (fun β _ => ?_)
          simp only [add_tsub_cancel_right]
      _ = ∑ α ∈ Finset.Nat.antidiagonalTuple n (m + 1),
            (∏ k, s k z ^ α k) * ∑ i ∈ Finset.univ.filter (fun i => 0 < α i), Hs i (α - Pi.single i 1) z := by
          simp only [Finset.sum_filter, Finset.mul_sum]
          exact Finset.sum_comm.trans (Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ => by
            split_ifs <;> simp)

end

end GlobalTheory.SkodaIter
