import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.TailBound
import ReciprocityTheory.AnalyticForms.LeviForms.MixedIntegralInclusionExclusion
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactRWSublevel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsomorphicLinesPotentialDifference

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB
open scoped ContDiff

noncomputable section

namespace LevelTowerAlt.Comparison₂

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem c2at (A : FinHolAtlas e X) {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hU : (A.chart j).symm y ∈ P.U x) : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  ((hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hy, hU⟩)).of_le (by
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    exact h2)

theorem levi_shift {F G : (Fin e → ℂ) → ℝ} {y : Fin e → ℂ} (hF : ContDiffAt ℝ 2 F y) (hG : ContDiffAt ℝ 2 G y) (a b : ℝ)
    (w : Fin e → ℂ) : levi (fun z => F z + a * G z + b) y w = levi F y w + a * levi G y w := by
  have h1 := TailChernBound.levi_lin 1 a hF hG w
  have h2 := TailChernBound.levi_lin 1 b ((contDiffAt_const (c := (1 : ℝ))).mul hF |>.add
    ((contDiffAt_const (c := a)).mul hG)) (contDiffAt_const (c := (1 : ℝ))) w
  have h0 : levi (fun _ : Fin e → ℂ => (1 : ℝ)) y w = 0 := by simp [levi]
  rw [h0, h1] at h2
  simpa using h2

variable [CompactSpace X] [T2Space X]

theorem term_zero (A : FinHolAtlas e X) (Θ : Fin e → LocPot X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X) (hΘ : ∀ i, IsPotential A (Θ i)) (hΘp : ∀ i, IsPosPot A (Θ i)) (hL : IsPotential A L)
    (hs : IsSection A L s) (hsnc : IsSNC A L s m W) (hle : ∀ y, logNormSec L s y ≤ 0) (C₁ C₆ : ℝ) (hC₁ : 0 ≤ C₁)
    (u : ℝ → Fin e → X → ℝ) (g : ℝ → X → ℝ)
    (hu : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (u t i)) ∧ (∀ i, IsPsh A (Θ i + LocPot.ofFun (u t i))) ∧
      ∀ i, ∀ y ∉ bdry s, -C₁ * Real.log (rW L s y) ≤ u t i y ∧ u t i y ≤ 0)
    (hg : ∀ᶠ t in 𝓝[>] (0 : ℝ), Continuous (g t) ∧ ∀ y ∉ bdry s, |g t y| ≤ C₆ * Real.log (rW L s y))
    (hg0 : ∀ K ⊆ (bdry s)ᶜ, IsCompact K → TendstoUniformlyOn g (fun _ => 0) (𝓝[>] 0) K) :
    Tendsto (fun t => mInt A (fun i => Θ i + LocPot.ofFun (u t i)) (g t)) (𝓝[>] 0) (𝓝 0) := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.tail_bound_statement_holds A Θ L s m W hΘ hΘp hL hs hsnc hle
  have hr : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hle
  have hlog : ∀ y, 0 ≤ Real.log (rW L s y) := fun y =>
    Real.log_nonneg ((Real.one_le_exp zero_le_one).trans (hr y))
  set M : ℝ := |C * (C₁ + 3) * Real.log (Real.exp 1) / Real.exp 1| with hM
  have hM0 : 0 ≤ M := abs_nonneg _
  have hT : Tendsto (fun R : ℝ => |C₆| * (C * (C₁ + 3)) * (Real.log R ^ 2 / R)) atTop (𝓝 0) := by
    simpa using ((Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero).const_mul (|C₆| * (C * (C₁ + 3)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR1, hR2⟩ := ((hT.eventually (gt_mem_nhds (half_pos hε))).and (eventually_ge_atTop (Real.exp 1))).exists
  set δ : ℝ := ε / (2 * (M + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hK := GlobalTheory.CompanionTheory.Ar.Giv.isCompact_rW_sublevel A L s hL hs R
  have hun := Metric.tendstoUniformlyOn_iff.1 (hg0 _ (fun y hy => hy.1) hK) δ hδ0
  filter_upwards [hu, hg, hun] with t ⟨hu1, hu2, hu3⟩ ⟨hg1, hg2⟩ hun
  have hpot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (u t i)) := fun i =>
    isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hu1 i))
  have hI := ((maMeasure_thm A _ hpot hu2).2 (g t) hg1.measurable).2 (mIntegrableCont A _ hpot _ hg1)
  have hnull := bdry_null A L s m W hL hs hsnc _ hpot
  have hmass := (hC C₁ (u t) hC₁ hu1 hu2 hu3 (Real.exp 1) le_rfl).1
  have htail := (hC C₁ (u t) hC₁ hu1 hu2 hu3 R hR2).2
  set μ := maMeasure A fun i => Θ i + LocPot.ofFun (u t i) with hμ
  have huniv : bdry s ∪ {y | Real.exp 1 ≤ rW L s y} = Set.univ := Set.eq_univ_of_forall fun y => Or.inr (hr y)
  rw [huniv] at hmass
  replace hmass : μ Set.univ ≤ ENNReal.ofReal M := hmass.trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
  have hBo : IsOpen (bdry s)ᶜ := by
    have h1 : (bdry s)ᶜ = ⋃ k : ℕ, {y | y ∉ bdry s ∧ rW L s y < k} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨fun h => (exists_nat_gt (rW L s y)).imp fun k hk => ⟨h, hk⟩, fun ⟨_, h, _⟩ => h⟩
    rw [h1]
    exact isOpen_iUnion fun k => (rW_open A L s hL hs).2 k
  have hE : MeasurableSet ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) := by
    have h1 : (bdry s)ᶜ ∩ {y | R ≤ rW L s y} = (bdry s)ᶜ \ {y | y ∉ bdry s ∧ rW L s y < R} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_sdiff, not_and, not_lt]
      exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
    rw [h1]
    exact hBo.measurableSet.diff ((rW_open A L s hL hs).2 R).measurableSet
  have hpt : ∀ᵐ y ∂μ, ENNReal.ofReal ‖g t y‖ ≤ ENNReal.ofReal δ + ENNReal.ofReal |C₆| *
      ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}).indicator (fun y => ENNReal.ofReal (Real.log (rW L s y))) y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    by_cases h : R ≤ rW L s y
    · rw [Set.indicator_of_mem (show y ∈ (bdry s)ᶜ ∩ {y | R ≤ rW L s y} from ⟨hy, h⟩),
        ← ENNReal.ofReal_mul (abs_nonneg _)]
      refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
      exact (hg2 y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hlog y))
    · refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
      have := hun y ⟨hy, (not_le.1 h).le⟩
      rw [dist_comm, dist_zero_right] at this
      exact this.le
  have hb : ∫⁻ y, ENNReal.ofReal ‖g t y‖ ∂μ ≤
      ENNReal.ofReal (δ * M + max (|C₆| * (C * (C₁ + 3) * Real.log R ^ 2 / R)) 0) := by
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator hE, ENNReal.ofReal_add (by positivity) (le_max_right _ _), ENNReal.ofReal_mul hδ0.le]
    refine add_le_add (by gcongr) ?_
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    gcongr
  rw [hI, dist_zero_right]
  refine (norm_integral_le_lintegral_norm _).trans_lt ?_
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hb).trans_lt ?_
  have h1 : δ * M < ε / 2 := by
    have : δ * (M + 1) = ε / 2 := by rw [hδ]; field_simp
    nlinarith
  have h2 : max (|C₆| * (C * (C₁ + 3) * Real.log R ^ 2 / R)) 0 < ε / 2 :=
    max_lt (by convert hR1 using 1; ring) (half_pos hε)
  linarith

set_option maxHeartbeats 1000000 in
theorem weak_zero (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hL : IsPotential A L)
    (hs : IsSection A L s) (hsnc : IsSNC A L s m W) (hle : ∀ y, logNormSec L s y ≤ 0) (P : Fin e → LocPot X)
    (hP : ∀ i, IsPotential A (P i)) (Q : ℝ → Fin e → LocPot X) (f : ℝ → Fin e → X → ℝ) (g : ℝ → X → ℝ)
    (C : Fin e → ℝ) (C₆ : ℝ)
    (hQ : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (f t i) ∧ IsPotential A (Q t i) ∧ (∀ x, (Q t i).U x = (P i).U x) ∧
      (∀ x, ∀ y ∈ (P i).U x, (Q t i).φ x y = (P i).φ x y + f t i y) ∧ IsPsh A (Q t i + Θ.rsmul (C i)) ∧
      ∀ y ∉ bdry s, -C i * Real.log (rW L s y) ≤ f t i y ∧ f t i y ≤ C i)
    (hg : ∀ᶠ t in 𝓝[>] (0 : ℝ), Continuous (g t) ∧ ∀ y ∉ bdry s, |g t y| ≤ C₆ * Real.log (rW L s y))
    (hg0 : ∀ K ⊆ (bdry s)ᶜ, IsCompact K → TendstoUniformlyOn g (fun _ => 0) (𝓝[>] 0) K) :
    Tendsto (fun t => mInt A (Q t) (g t)) (𝓝[>] 0) (𝓝 0) := by
  classical
  choose D hD0 hD _ using fun i => TailBoundAlt.exists_psh_chern_bound A Θ (P i) hΘ hΘp (hP i)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ i, (|C i| + D i) + 1 := ⟨_, rfl⟩
  have hci : ∀ i, |C i| + D i + 1 ≤ c := fun i => by
    have := Finset.single_le_sum (f := fun i => |C i| + D i) (fun i _ => add_nonneg (abs_nonneg _) (hD0 i))
      (Finset.mem_univ i)
    linarith
  have hc0 : 0 < c := by
    have := Finset.sum_nonneg (s := Finset.univ) (f := fun i => |C i| + D i) fun i _ => add_nonneg (abs_nonneg _) (hD0 i)
    linarith
  have hΘ' : IsPotential A (Θ.rsmul c) := isPotentialRsmul A c Θ hΘ
  have hΘ'p : IsPosPot A (Θ.rsmul c) := fun x j y hy w hw => by
    have := TailChernBound.levi_smul' c (c2at A hΘ x j hy.1 hy.2) w
    exact lt_of_lt_of_eq (mul_pos hc0 (hΘp x j y hy w hw)) this.symm
  have hT : ∀ i, IsPotential A (P i + Θ.rsmul c) := fun i => isPotentialAdd A _ _ (hP i) hΘ'
  have hTp : ∀ i, IsPosPot A (P i + Θ.rsmul c) := fun i x j y hy w hw => by
    have h1 := hD i x j y ⟨hy.1, hy.2.2, hy.2.1⟩ w
    have h2 := levi_shift (c2at A (isPotentialAdd A _ _ (isPotentialRsmul A (D i) Θ hΘ) (hP i)) x j hy.1 ⟨hy.2.2, hy.2.1⟩)
      (c2at A hΘ x j hy.1 hy.2.2) (c - D i) 0 w
    have h3 : (P i + Θ.rsmul c).φ x ∘ (A.chart j).symm = fun z => ((Θ.rsmul (D i) + P i).φ x ∘ (A.chart j).symm) z +
        (c - D i) * (Θ.φ x ∘ (A.chart j).symm) z + 0 := by
      funext z
      show (P i).φ x _ + c * Θ.φ x _ = D i * Θ.φ x _ + (P i).φ x _ + (c - D i) * Θ.φ x _ + 0
      ring
    rw [h3, h2]
    have := mul_pos (show 0 < c - D i by linarith [hci i, abs_nonneg (C i)]) (hΘp x j y ⟨hy.1, hy.2.2⟩ w hw)
    linarith
  have hlog : ∀ y, 1 ≤ Real.log (rW L s y) := fun y => by
    rw [Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (rW_ge L s hle y))]
    exact rW_ge L s hle y
  have hQ' := eventually_all.2 hQ
  have hsm : ∀ {v : X → ℝ}, A.Smooth v → A.Smooth fun y => v y - c := fun hv j => (hv j).sub contDiffOn_const
  have hterm : ∀ S : Finset (Fin e), Tendsto (fun t => mInt A (fun i => (if i ∈ S then P i + Θ.rsmul c else Θ.rsmul c) +
      LocPot.ofFun (if i ∈ S then fun y => f t i y - c else fun _ => 0)) (g t)) (𝓝[>] 0) (𝓝 0) := by
    intro S
    refine term_zero A (fun i => if i ∈ S then P i + Θ.rsmul c else Θ.rsmul c) L s m W
      (fun i => by split_ifs; exacts [hT i, hΘ']) (fun i => by split_ifs; exacts [hTp i, hΘ'p]) hL hs hsnc hle (2 * c) C₆
      (by linarith) (fun t i => if i ∈ S then fun y => f t i y - c else fun _ => 0) g ?_ hg hg0
    filter_upwards [hQ'] with t ht
    refine ⟨fun i => ?_, fun i => ?_, fun i y hy => ?_⟩
    · split_ifs
      exacts [hsm (ht i).1, fun j => contDiffOn_const]
    · split_ifs
      · obtain ⟨-, h2, h3, h4, h5, -⟩ := ht i
        intro x j y hy w
        have hyP : (A.chart j).symm y ∈ (P i).U x := hy.2.1.1
        have hyT : (A.chart j).symm y ∈ Θ.U x := hy.2.1.2
        have hyQ : (A.chart j).symm y ∈ (Q t i + Θ.rsmul (C i)).U x := ⟨(h3 x).symm ▸ hyP, hyT⟩
        have a1 := h5 x j y ⟨hy.1, hyQ⟩ w
        have a2 := levi_shift (c2at A (isPotentialAdd A _ _ h2 (isPotentialRsmul A (C i) Θ hΘ)) x j hy.1 hyQ)
          (c2at A hΘ x j hy.1 hyT) (c - C i) (-c) w
        have a3 : (P i + Θ.rsmul c + LocPot.ofFun fun y => f t i y - c).φ x ∘ (A.chart j).symm =ᶠ[𝓝 y]
            fun z => ((Q t i + Θ.rsmul (C i)).φ x ∘ (A.chart j).symm) z +
              (c - C i) * (Θ.φ x ∘ (A.chart j).symm) z + -c := by
          filter_upwards [((A.chart j).isOpen_inter_preimage_symm ((P i).isOpen_U x)).mem_nhds ⟨hy.1, hyP⟩] with z hz
          show (P i).φ x _ + c * Θ.φ x _ + (f t i _ - c) = (Q t i).φ x _ + C i * Θ.φ x _ + (c - C i) * Θ.φ x _ + -c
          rw [h4 x _ hz.2]
          ring
        rw [levi_congr a3, a2]
        have := mul_nonneg (show 0 ≤ c - C i by linarith [hci i, le_abs_self (C i), hD0 i])
          (TailBoundAlt.isPsh_of_isPosPot A Θ hΘp x j y ⟨hy.1, hyT⟩ w)
        linarith
      · refine TailBoundAlt.isPsh_congr A _ _ (TailBoundAlt.isPsh_of_isPosPot A _ hΘ'p) (fun x y hy => hy.1) ?_
        funext x y
        exact add_zero _
    · have h1 := hlog y
      split_ifs
      · obtain ⟨h2, h3⟩ := (ht i).2.2.2.2.2 y hy
        have h4 := hci i
        have h5 := le_abs_self (C i)
        have h6 := hD0 i
        constructor
        · nlinarith
        · linarith
      · exact ⟨by nlinarith, le_rfl⟩
  have hsum := tendsto_finsetSum Finset.univ fun S (_ : S ∈ Finset.univ) => (hterm S).const_mul ((-1 : ℝ) ^ (e - S.card))
  simp only [mul_zero, Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hQ', hg] with t ht hgt
  have hΦ : ∀ i, IsPotential A (P i + Θ.rsmul c + LocPot.ofFun fun y => f t i y - c) := fun i =>
    isPotentialAdd A _ _ (hT i) (isPotential_ofFun A _ (hsm (ht i).1))
  have h1 := mixed_integral_inclusion_exclusion A (Θ.rsmul c) _ hΘ' hΦ (g t) hgt.1
  have h2 := (mInt_congr_samePot e X A Set.univ (Q t)
    (fun i => P i + Θ.rsmul c + (LocPot.ofFun fun y => f t i y - c) + (Θ.rsmul c).rsmul (-1)) (g t) (g t)
    (by simp [IsNull]) (fun i x _ => ⟨(P i).U x, (P i).isOpen_U x, (P i).mem_U x, fun _ => c,
      fun j => analyticOnNhd_const, fun y hy => by
        show (Q t i).φ x y - ((P i).φ x y + c * Θ.φ x y + (f t i y - c) + -1 * (c * Θ.φ x y)) = c
        rw [(ht i).2.2.2.1 x y hy]
        ring⟩)
    (fun i x _ => GlobalTheory.CompanionTheory.Ar.Cmp.OneModel.isC2At_of_isPotential A
      (isPotentialAdd A _ _ (hΦ i) (isPotentialRsmul A (-1) _ hΘ')) x) (fun _ _ => rfl)).1
  rw [h2, h1]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  unfold mInt integralWith locDens
  have : ∀ i, ((if i ∈ S then P i + Θ.rsmul c else Θ.rsmul c) +
      LocPot.ofFun (if i ∈ S then fun y => f t i y - c else fun _ => 0)).φ =
      (if i ∈ S then P i + Θ.rsmul c + LocPot.ofFun fun y => f t i y - c else Θ.rsmul c).φ := fun i => by
    split_ifs
    · rfl
    · funext x y
      exact add_zero _
  simp only [this]

end LevelTowerAlt.Comparison₂
