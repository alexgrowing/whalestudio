import Development.WeilBound.ThetaLifts.LatticeBasics.RegOfBound
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected

noncomputable section

open Filter Topology Set GlobalTheory.Cont GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Khead

variable {X : Type} [TopologicalSpace X] {h : X → ℝ}

private theorem regOn_mono {g : ℂ → X → ℂ} {S T : Set ℂ} (hg : An.RegOn h g S) (hT : T ⊆ S) :
    An.RegOn h g T := by
  obtain ⟨C, N, hC⟩ := hg.grow
  exact ⟨fun x => (hg.hol x).mono hT, hg.cont.mono (prod_mono hT subset_rfl),
    ⟨C, N, fun s hs x => hC s (hT hs) x⟩⟩

private theorem regOn_congr {g G : ℂ → X → ℂ} {S : Set ℂ} (hg : An.RegOn h g S)
    (he : ∀ s ∈ S, ∀ x, G s x = g s x) : An.RegOn h G S := by
  obtain ⟨C, N, hC⟩ := hg.grow
  refine ⟨fun x => (hg.hol x).congr fun s hs => he s hs x, ?_, ⟨C, N, fun s hs x => ?_⟩⟩
  · exact hg.cont.congr fun y hy => he y.1 hy.1 y.2
  · rw [he s hs x]
    exact hC s hs x

private theorem regOn_polynomial_mul_of_subset_ball {g : ℂ → X → ℂ} {S : Set ℂ} (hg : An.RegOn h g S) (c : ℂ) (R : ℝ)
    (hS : S ⊆ Metric.ball c R) (q : Polynomial ℂ) :
    An.RegOn h (fun s x => q.eval s * g s x) S := by
  obtain ⟨C, N, hC⟩ := hg.grow
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn
    q.continuous.continuousOn
  refine ⟨fun x => q.differentiable.differentiableOn.mul (hg.hol x), ?_, ⟨max M 0 * C, N, fun s hs x => ?_⟩⟩
  · exact (q.continuous.comp continuous_fst).continuousOn.mul hg.cont
  · have h1 : ‖q.eval s‖ ≤ max M 0 :=
      (hM s (Metric.ball_subset_closedBall (hS hs))).trans (le_max_left _ _)
    rw [norm_mul, mul_assoc]
    exact mul_le_mul h1 (hC s hs x) (norm_nonneg _) (le_max_right _ _)

private theorem exists_local_regularization_of_reg_right_half {g : ℂ → X → ℂ}
    (hp : ∀ s₀ : ℂ, ∃ (k : ℕ) (H : ℂ → X → ℂ), An.Reg h H s₀ ∧ ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * g s x)
    {t : ℝ} (hr : ∀ s : ℂ, t < s.re → An.Reg h g s) (z : ℂ) :
    ∃ (k : ℕ) (H : ℂ → X → ℂ) (ρ : ℝ), 0 < ρ ∧ An.RegOn h H (Metric.ball z ρ) ∧
      ∀ s ∈ Metric.ball z ρ, (s ≠ z ∨ t < z.re) → ∀ x, H s x = (s - z) ^ k * g s x := by
  by_cases hz : t < z.re
  · obtain ⟨S, hS, hR⟩ := hr z hz
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hS
    exact ⟨0, g, ρ, hρ, regOn_mono hR hsub, fun s _ _ x => by simp⟩
  · obtain ⟨k, H, ⟨S, hS, hR⟩, hev⟩ := hp z
    obtain ⟨ρ1, hρ1, hsub⟩ := Metric.mem_nhds_iff.mp hS
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hE⟩ := hev
    refine ⟨k, H, min ρ1 ε, lt_min hρ1 hε,
      regOn_mono hR ((Metric.ball_subset_ball (min_le_left _ _)).trans hsub), fun s hs hne x => ?_⟩
    exact hE (lt_of_lt_of_le (Metric.mem_ball.mp hs) (min_le_right _ _)) (hne.resolve_right hz) x

theorem strip (h1 : ∀ x, 1 ≤ h x) {g : ℂ → X → ℂ}
    (hp : ∀ s₀ : ℂ, ∃ (k : ℕ) (H : ℂ → X → ℂ), An.Reg h H s₀ ∧ ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * g s x)
    {t : ℝ} (hr : ∀ s : ℂ, t < s.re → An.Reg h g s) (s₀ : ℂ) :
    ∃ (U : Set ℂ) (p : Polynomial ℂ) (G : ℂ → X → ℂ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ p ≠ 0 ∧
      (∀ s ∈ U, An.Reg h G s) ∧ ∀ s : ℂ, t < s.re → ∀ x, G s x = p.eval s * g s x := by
  classical
  choose k H ρ hρ hReg hEq using exists_local_regularization_of_reg_right_half hp hr
  have hKc : IsCompact ((fun r : ℝ => s₀ + (r : ℂ)) '' Icc 0 (|t - s₀.re| + 1)) :=
    isCompact_Icc.image (continuous_const.add Complex.continuous_ofReal)
  obtain ⟨F, hFK, hKF⟩ := hKc.elim_nhds_subcover (fun z => Metric.ball z (ρ z))
    (fun z _ => Metric.ball_mem_nhds z (hρ z))
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric
    (c := fun i : F => Metric.ball (i : ℂ) (ρ i)) hKc (fun i => Metric.isOpen_ball) (by
      intro w hw
      obtain ⟨z, hzF, hwz⟩ := mem_iUnion₂.mp (hKF hw)
      exact mem_iUnion.mpr ⟨⟨z, hzF⟩, hwz⟩)
  let q : ℂ → Polynomial ℂ := fun z => ∏ z' ∈ F.erase z, (Polynomial.X - Polynomial.C z') ^ k z'
  let p : Polynomial ℂ := ∏ z' ∈ F, (Polynomial.X - Polynomial.C z') ^ k z'
  have hpq : ∀ z ∈ F, ∀ s, p.eval s = (s - z) ^ k z * (q z).eval s := by
    intro z hz s
    show Polynomial.eval s (∏ z' ∈ F, (Polynomial.X - Polynomial.C z') ^ k z') = _
    rw [← Finset.mul_prod_erase F _ hz]
    simp [q, Polynomial.eval_prod]
  have hp0 : p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun z _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero z)
  let G : ℂ → X → ℂ := fun s x => if s ∈ F then (q s).eval s * H s s x else p.eval s * g s x
  have hloc : ∀ z ∈ F, ∀ s ∈ Metric.ball z (ρ z), ∀ x, G s x = (q z).eval s * H z s x := by
    intro z hz s hs x
    by_cases hsF : s ∈ F
    · by_cases hsz : s = z
      · subst hsz
        simp [G, hsF]
      · have e1 : G s x = (q s).eval s * H s s x := by simp [G, hsF]
        rw [e1]
        let φ1 : ℂ → ℂ := fun w => (q s).eval w * H s w x
        let φ2 : ℂ → ℂ := fun w => (q z).eval w * H z w x
        have c1 : ContinuousAt φ1 s := (q s).continuous.continuousAt.mul
          (((hReg s).hol x s (Metric.mem_ball_self (hρ s))).differentiableAt
            (Metric.ball_mem_nhds s (hρ s))).continuousAt
        have c2 : ContinuousAt φ2 s := (q z).continuous.continuousAt.mul
          (((hReg z).hol x s hs).differentiableAt (Metric.isOpen_ball.mem_nhds hs)).continuousAt
        have hn : ∀ᶠ w in 𝓝 s, w ∈ Metric.ball s (ρ s) ∧ w ∈ Metric.ball z (ρ z) ∧ w ∈ ({z}ᶜ : Set ℂ) := by
          filter_upwards [Metric.ball_mem_nhds s (hρ s), Metric.isOpen_ball.mem_nhds hs,
            isClosed_singleton.isOpen_compl.mem_nhds hsz] with w ha hb hc
          exact ⟨ha, hb, hc⟩
        have hev : φ2 =ᶠ[𝓝[≠] s] φ1 := by
          rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
          filter_upwards [hn] with w ⟨hw1, hw2, hw3⟩ hws
          simp only [φ1, φ2]
          rw [hEq s w hw1 (Or.inl hws) x, hEq z w hw2 (Or.inl hw3) x, ← mul_assoc, ← mul_assoc,
            mul_comm ((q s).eval w), mul_comm ((q z).eval w), ← hpq s hsF w, ← hpq z hz w]
        exact tendsto_nhds_unique (c1.tendsto.mono_left nhdsWithin_le_nhds)
          ((c2.tendsto.mono_left nhdsWithin_le_nhds).congr' hev)
    · have hsz : s ≠ z := fun h' => hsF (h' ▸ hz)
      simp only [G, hsF, if_false]
      rw [hEq z s hs (Or.inl hsz) x, hpq z hz s]
      ring
  have hright : ∀ s : ℂ, t < s.re → ∀ x, G s x = p.eval s * g s x := by
    intro s hs x
    by_cases hsF : s ∈ F
    · simp only [G, hsF, if_true]
      rw [hEq s s (Metric.mem_ball_self (hρ s)) (Or.inr hs) x, hpq s hsF s]
      ring
    · simp [G, hsF]
  have hRopen : IsOpen (rightOf t) := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨(⋃ r ∈ Ici (0:ℝ), (fun w : ℂ => w - r) ⁻¹' Metric.ball s₀ (min δ 1)) ∪ rightOf t, p, G,
    ?_, ?_, ?_, hp0, ?_, hright⟩
  · exact (isOpen_biUnion fun r _ =>
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)).union hRopen
  · refine ⟨⟨t, subset_union_right⟩, fun s hs r hr0 => ?_⟩
    rcases hs with hs | hs
    · obtain ⟨r', hr', hmem⟩ := mem_iUnion₂.mp hs
      left
      refine mem_iUnion₂.mpr ⟨r' + r, add_nonneg hr' hr0, ?_⟩
      have e : s + (r : ℂ) - ((r' + r : ℝ) : ℂ) = s - r' := by
        push_cast
        ring
      rw [mem_preimage, e]
      exact hmem
    · right
      simp only [rightOf, mem_setOf_eq] at hs ⊢
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
  · left
    refine mem_iUnion₂.mpr ⟨0, Set.mem_Ici.mpr le_rfl, ?_⟩
    simp [hδ]
  · intro s hs
    by_cases hst : t < s.re
    · obtain ⟨S, hS, hR⟩ := hr s hst
      refine ⟨S ∩ Metric.ball s 1 ∩ rightOf t,
        inter_mem (inter_mem hS (Metric.ball_mem_nhds s one_pos)) (hRopen.mem_nhds hst), ?_⟩
      exact regOn_congr (regOn_polynomial_mul_of_subset_ball (regOn_mono hR fun w hw => hw.1.1) s 1 (fun w hw => hw.1.2) p)
        fun w hw x => hright w hw.2 x
    · have hs1 := hs.resolve_right hst
      obtain ⟨r, hr0, hmem⟩ := mem_iUnion₂.mp hs1
      simp only [mem_preimage, Metric.mem_ball, dist_eq_norm] at hmem
      have hre : |(s - r - s₀).re| ≤ ‖s - r - s₀‖ := Complex.abs_re_le_norm _
      simp only [Complex.sub_re, Complex.ofReal_re] at hre
      have hst' : s.re ≤ t := not_lt.mp hst
      have hc : s₀ + (r : ℂ) ∈ (fun r : ℝ => s₀ + (r : ℂ)) '' Icc 0 (|t - s₀.re| + 1) := by
        refine ⟨r, ⟨hr0, ?_⟩, rfl⟩
        have h2 := neg_abs_le (s.re - r - s₀.re)
        have h3 := le_abs_self (t - s₀.re)
        have h4 : min δ 1 ≤ 1 := min_le_right _ _
        linarith
      obtain ⟨i, hi⟩ := hleb _ hc
      have hsb : s ∈ Metric.ball (s₀ + r) δ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have e : s - (s₀ + (r : ℂ)) = s - r - s₀ := by ring
        rw [e]
        exact lt_of_lt_of_le hmem (min_le_left _ _)
      have hsz := hi hsb
      refine ⟨Metric.ball (i : ℂ) (ρ i), Metric.isOpen_ball.mem_nhds hsz, ?_⟩
      exact regOn_congr (regOn_polynomial_mul_of_subset_ball (hReg i) i (ρ i) subset_rfl (q i)) fun w hw x => hloc i i.2 w hw x

theorem diff_cont_of_reg {G : ℂ → X → ℂ} {U : Set ℂ} (hU : ∀ s ∈ U, An.Reg h G s) :
    (∀ x, DifferentiableOn ℂ (G · x) U) ∧ ContinuousOn (fun y : ℂ × X => G y.1 y.2) (U ×ˢ univ) := by
  refine ⟨fun x s hs => ?_, fun y hy => ?_⟩
  · obtain ⟨S, hS, hR⟩ := hU s hs
    exact ((hR.hol x s (mem_of_mem_nhds hS)).differentiableAt hS).differentiableWithinAt
  · obtain ⟨S, hS, hR⟩ := hU y.1 hy.1
    exact (hR.cont.continuousAt (prod_mem_nhds hS univ_mem)).continuousWithinAt

end PositivityTheory.SiegelWeilFormula.Khead
