import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormSubOneMulRiemannZetaLe
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.LogDerivHigher

lemma extend (K : ℝ) (U : Set ℂ) (hU : IsOpen U) (Z : Finset ℂ) :
    ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (U \ Z) → (∀ z ∈ U \ (Z : Set ℂ), ‖g z‖ ≤ K) →
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ (∀ z, z ∉ Z → G z = g z) ∧ ∀ z ∈ U, ‖G z‖ ≤ K := by
  induction Z using Finset.induction_on with
  | empty => intro g h1 h2; exact ⟨g, by simpa using h1, fun _ _ => rfl, by simpa using h2⟩
  | insert a Z ha ih =>
    intro g h1 h2
    have hset : U \ (↑(insert a Z) : Set ℂ) = (U \ Z) \ {a} := by
      ext z; simp; tauto
    rw [hset] at h1 h2
    by_cases haU : a ∈ U
    · have ho : IsOpen (U \ (Z : Set ℂ)) := hU.sdiff Z.finite_toSet.isClosed
      have hn : U \ (Z : Set ℂ) ∈ 𝓝 a := ho.mem_nhds ⟨haU, by simpa using ha⟩
      have hd := Complex.differentiableOn_update_limUnder_of_bddAbove hn h1
        ⟨K, by rintro _ ⟨z, hz, rfl⟩; exact h2 z hz⟩
      obtain ⟨G, g1, g2, g3⟩ := ih _ hd (fun z hz => by
        by_cases hza : z = a
        · subst hza
          have hc : Tendsto (fun w => ‖Function.update g z (limUnder (𝓝[≠] z) g) w‖) (𝓝[≠] z)
              (𝓝 ‖Function.update g z (limUnder (𝓝[≠] z) g) z‖) :=
            ((hd.differentiableAt hn).continuousAt.norm.tendsto).mono_left nhdsWithin_le_nhds
          refine le_of_tendsto hc ?_
          filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with w hw hw'
          rw [Function.update_of_ne hw]
          exact h2 w ⟨hw', hw⟩
        · rw [Function.update_of_ne hza]; exact h2 z ⟨hz, hza⟩)
      refine ⟨G, g1, fun z hz => ?_, g3⟩
      rw [Finset.mem_insert, not_or] at hz
      rw [g2 z hz.2, Function.update_of_ne hz.1]
    · have : (U \ (Z : Set ℂ)) \ {a} = U \ Z := by
        ext z; constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, fun e => haU (by rw [← Set.mem_singleton_iff.1 e]; exact h.1)⟩
      rw [this] at h1 h2
      obtain ⟨G, g1, g2, g3⟩ := ih g h1 h2
      exact ⟨G, g1, fun z hz => g2 z fun h => hz (Finset.mem_insert_of_mem h), g3⟩

lemma cauchy (K : ℝ) (U : Set ℂ) (hU : IsOpen U) (Z : Finset ℂ) (g : ℂ → ℂ)
    (h1 : DifferentiableOn ℂ g (U \ Z)) (h2 : ∀ z ∈ U \ (Z : Set ℂ), ‖g z‖ ≤ K)
    (s : ℂ) (R : ℝ) (hR : 0 < R) (hs : s ∉ Z) (hsub : Metric.closedBall s R ⊆ U) (k : ℕ) :
    ‖iteratedDeriv k g s‖ ≤ k.factorial * K / R ^ k := by
  obtain ⟨G, g1, g2, g3⟩ := extend K U hU Z g h1 h2
  have hev : g =ᶠ[𝓝 s] G := by
    filter_upwards [Z.finite_toSet.isClosed.isOpen_compl.mem_nhds hs] with z hz
    exact (g2 z hz).symm
  rw [hev.iteratedDeriv_eq]
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR ?_
    fun z hz => g3 z (hsub (Metric.sphere_subset_closedBall hz))
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_ball s hR.ne']
  exact g1.mono hsub

lemma hasDerivAt_pole (c w s : ℂ) (k : ℕ) (h : s ≠ w) :
    HasDerivAt (fun z => c / (z - w) ^ (k + 1)) (-((k + 1 : ℕ) : ℂ) * (c / (s - w) ^ (k + 1 + 1))) s := by
  have h0 : s - w ≠ 0 := sub_ne_zero.2 h
  have h1 := (hasDerivAt_const s c).fun_div (((hasDerivAt_id' s).sub_const w).fun_pow (k + 1))
    (pow_ne_zero _ h0)
  refine h1.congr_deriv ?_
  simp only [Nat.add_sub_cancel]
  field_simp
  push_cast
  ring

lemma iter (f : ℕ → ℂ) (hf : LSeries.abscissaOfAbsConv f ≤ 1) (e : ℂ) (Z : Finset ℂ) (m : ℂ → ℂ)
    (hZ : ∀ w ∈ Z, w.re ≤ 1) (g : ℂ → ℂ)
    (hg : ∀ s : ℂ, 1 < s.re → g s = -(LSeries f s - e / (s - 1) + ∑ w ∈ Z, m w / (s - w)))
    (k : ℕ) : ∀ s : ℂ, 1 < s.re → iteratedDeriv k g s = (-1) ^ (k + 1) *
      (LSeries (LSeries.logMul^[k] f) s + k.factorial *
        (- (e / (s - 1) ^ (k + 1)) + ∑ w ∈ Z, m w / (s - w) ^ (k + 1))) := by
  induction k with
  | zero => intro s hs; simp [hg s hs]; ring
  | succ k ih =>
    intro s hs
    have hev : iteratedDeriv k g =ᶠ[𝓝 s] fun s => (-1) ^ (k + 1) *
      (LSeries (LSeries.logMul^[k] f) s + k.factorial *
        (- (e / (s - 1) ^ (k + 1)) + ∑ w ∈ Z, m w / (s - w) ^ (k + 1))) := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
      exact ih z hz
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have a1 : LSeries.abscissaOfAbsConv (LSeries.logMul^[k] f) < s.re := by
      rw [LSeries.absicssaOfAbsConv_logPowMul]
      exact hf.trans_lt (by exact_mod_cast hs)
    have d1 := LSeries_hasDerivAt a1
    have d2 := hasDerivAt_pole e 1 s k (by rintro rfl; simp at hs)
    have d3 := HasDerivAt.fun_sum (u := Z) fun w hw => hasDerivAt_pole (m w) w s k
      (by rintro rfl; linarith [hZ _ hw])
    have d4 := (d1.fun_add ((d2.fun_neg.fun_add d3).const_mul (k.factorial : ℂ))).const_mul
      ((-1 : ℂ) ^ (k + 1))
    rw [d4.deriv, Function.iterate_succ', ← Finset.mul_sum, Nat.factorial_succ]
    simp only [Function.comp_apply]
    push_cast
    ring

lemma derSeries_eq (c : ℕ → ℂ) (k : ℕ) (s : ℂ) :
    LSeries (LSeries.logMul^[k] (c * fun n : ℕ => ((Λ n : ℝ) : ℂ))) s
      = k.factorial * derSeries c k s := by
  have h : ∀ (f : ℕ → ℂ) (k n : ℕ), (LSeries.logMul^[k] f) n = (Complex.log n) ^ k * f n := by
    intro f k n
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', LSeries.logMul, ih]; ring
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [derSeries, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, h, cpow_neg, ← Complex.natCast_log, Pi.mul_apply]
    field_simp

lemma growth_triv : ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] (z : ℂ), -(7 / 4 : ℝ) ≤ z.re →
    ‖LFunctionTrivChar₁ q z‖ ≤ B * (q : ℝ) ^ 5 * (‖z‖ + 2) ^ 5 := by
  obtain ⟨B, hB, G⟩ := ZetaLeft.norm_sub_one_mul_riemannZeta_le
  refine ⟨B + 1, by positivity, fun q _ z hz => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hP : ∀ s : ℂ, -(7 / 4 : ℝ) ≤ s.re →
      ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ (q : ℝ) ^ 5 := by
    intro s hs
    rw [norm_prod]
    calc _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) ^ 3 := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
          have hp' := Nat.prime_of_mem_primeFactors hp
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
          refine (norm_sub_le _ _).trans ?_
          rw [norm_one, Complex.norm_natCast_cpow_of_pos hp'.pos]
          have : (p : ℝ) ^ (-s).re ≤ (p : ℝ) ^ ((2 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [neg_re]; push_cast; linarith)
          rw [Real.rpow_natCast] at this
          nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg (p : ℝ))]
      _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ 3 := by rw [Finset.prod_pow, Nat.cast_prod]
      _ ≤ (q : ℝ) ^ 3 := by
          gcongr
          exact Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)
      _ ≤ _ := pow_le_pow_right₀ hq (by norm_num)
  have h5 : (1 : ℝ) ≤ (‖z‖ + 2) ^ 5 := one_le_pow₀ (by linarith [norm_nonneg z])
  have hq5 : (0 : ℝ) ≤ (q : ℝ) ^ 5 := by positivity
  by_cases h1 : z = 1
  · have := hP 1 (by norm_num)
    simp only [cpow_neg_one] at this
    have e : LFunctionTrivChar₁ q z = ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) := by
      rw [h1, LFunctionTrivChar₁, Function.update_self]
    rw [e]
    refine this.trans ?_
    calc (q : ℝ) ^ 5 = 1 * (q : ℝ) ^ 5 * 1 := by ring
      _ ≤ _ := by gcongr; linarith
  · rw [LFunctionTrivChar₁, Function.update_of_ne h1, LFunctionTrivChar_eq_mul_riemannZeta h1,
      mul_left_comm, norm_mul]
    calc _ ≤ (q : ℝ) ^ 5 * (B * (‖z‖ + 2) ^ 5) :=
          mul_le_mul (hP z hz) (G z hz h1) (norm_nonneg _) hq5
      _ = B * (q : ℝ) ^ 5 * (‖z‖ + 2) ^ 5 := by ring
      _ ≤ _ := by gcongr; linarith

lemma exists_entire : ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, -(7 / 4 : ℝ) ≤ z.re → ‖F z‖ ≤ B * (q : ℝ) ^ 5 * (‖z‖ + 2) ^ 5) ∧
      (∀ z : ℂ, z.re = 2 → ‖LFunction χ z‖ ≤ ‖F z‖) ∧
      (∀ z : ℂ, F z = 0 ↔ (χ ≠ 1 ∨ z ≠ 1) ∧ LFunction χ z = 0) ∧
      (∀ z : ℂ, F z = 0 → analyticOrderNatAt F z = ord χ z) ∧
      ∀ s : ℂ, 1 < s.re → deriv F s / F s =
        deriv (LFunction χ) s / LFunction χ s + (if χ = 1 then 1 else 0) / (s - 1) := by
  obtain ⟨B, hB, G⟩ := growth_triv
  obtain ⟨B', hB', G'⟩ := norm_LFunction_le_poly_left
  refine ⟨B + B', by positivity, fun q _ χ => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  by_cases hχ : χ = 1
  · subst hχ
    have hF : ∀ z, z ≠ 1 → LFunctionTrivChar₁ q z
        = (z - 1) * LFunction (1 : DirichletCharacter ℂ q) z := fun z hz => by
      rw [LFunctionTrivChar₁, Function.update_of_ne hz]
    have hne : ∀ z, LFunctionTrivChar₁ q z = 0 → z ≠ 1 := fun z hz h =>
      LFunctionTrivChar₁_apply_one_ne_zero q (h ▸ hz)
    refine ⟨LFunctionTrivChar₁ q, differentiable_LFunctionTrivChar₁ q, fun z hz => ?_,
      fun z hz => ?_, fun z => ?_, fun z hz => ?_, fun s hs => ?_⟩
    · refine (G q z hz).trans ?_
      gcongr; linarith
    · rw [hF z (by rintro rfl; norm_num at hz), norm_mul]
      refine le_mul_of_one_le_left (norm_nonneg _) ?_
      have := Complex.re_le_norm (z - 1)
      rw [sub_re, hz, one_re] at this
      linarith
    · constructor
      · intro h
        have h1 := hne z h
        rw [hF z h1] at h
        exact ⟨Or.inr h1, (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h1)⟩
      · rintro ⟨h1, h2⟩
        rw [hF z (h1.resolve_left (by simp)), h2, mul_zero]
    · have h1 := hne z hz
      have hev : LFunctionTrivChar₁ q =ᶠ[𝓝 z]
          (fun z => z - 1) * LFunction (1 : DirichletCharacter ℂ q) := by
        filter_upwards [isOpen_ne.mem_nhds h1] with w hw
        exact hF w hw
      have a1 : AnalyticAt ℂ (fun z : ℂ => z - 1) z := by fun_prop
      have a2 : AnalyticAt ℂ (LFunction (1 : DirichletCharacter ℂ q)) z := by
        refine DifferentiableOn.analyticAt (s := {1}ᶜ) (fun w hw => ?_) (isOpen_ne.mem_nhds h1)
        exact (differentiableAt_LFunction _ w (Or.inl hw)).differentiableWithinAt
      unfold ord analyticOrderNatAt
      rw [analyticOrderAt_congr hev, analyticOrderAt_mul a1 a2,
        a1.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 h1), zero_add]
    · have h1 : s ≠ 1 := by rintro rfl; simp at hs
      have h2 : LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 :=
        LFunction_ne_zero_of_one_le_re _ (Or.inr h1) hs.le
      have h3 := sub_ne_zero.2 h1
      rw [deriv_LFunctionTrivChar₁_apply_of_ne_one q h1, hF s h1, if_pos rfl, LFunctionTrivChar]
      field_simp
  · refine ⟨LFunction χ, differentiable_LFunction hχ, fun z hz => ?_, fun _ _ => le_rfl,
      fun z => by simp [hχ], fun _ _ => rfl, fun s _ => by simp [hχ]⟩
    refine (G' q χ hχ z hz).trans ?_
    have h2 : (1 : ℝ) ≤ ‖z‖ + 2 := by linarith [norm_nonneg z]
    gcongr
    · linarith
    all_goals first | assumption | norm_num

theorem main : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ) (k : ℕ), 1 < σ → σ ≤ 2 → (zerosDisc χ (2 + t * I) 3).Finite ∧ (∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℝ)) ≤ C * Real.log (q * (|t| + 2)) ∧ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k (σ + t * I) - (if χ = 1 then 1 / ((σ : ℂ) + t * I - 1) ^ (k + 1) else 0) + ∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℂ) / ((σ : ℂ) + t * I - w) ^ (k + 1)‖ ≤ C * Real.log (q * (|t| + 2)) / σ ^ k := by
  obtain ⟨C, hC, H⟩ := LWide.disc (2 / 3) (4 / 5) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B, hB, G⟩ := exists_entire
  refine ⟨C * (2 * (1 + |Real.log (2048 * B)|) + 5), by positivity, ?_⟩
  intro q _ χ σ t k hs1 hs2
  obtain ⟨F, hF, f1, f2, f3, f4, f5⟩ := G q χ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set c : ℂ := 2 + t * I with hc
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hcre : c.re = 2 := by simp [hc]
  have hcn : ‖c‖ ≤ 2 + |t| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp
  have hlow : 1 / 2 ≤ ‖F c‖ := by
    have := LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)
    rw [hcre] at this
    linarith [f2 c hcre]
  have ht := abs_nonneg t
  set X : ℝ := q * (|t| + 2) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hlX : 1 / 2 ≤ Real.log X := by
    have := Real.log_le_log (by norm_num) hX2
    linarith [Real.log_two_gt_d9]
  have hpos : 0 < ‖F c‖ := by linarith
  obtain ⟨h1, h2, h3⟩ := H F c (15 / 4) (1024 * B * X ^ 5) (by norm_num)
    hF (norm_pos_iff.1 hpos) (fun z hz => by
      have hre : -(7 / 4 : ℝ) ≤ z.re := by
        have := (abs_le.1 ((Complex.abs_re_le_norm (z - c)).trans hz)).1
        rw [sub_re, hcre] at this
        linarith
      refine (f1 z hre).trans ?_
      have hzn : ‖z‖ + 2 ≤ 4 * (|t| + 2) := by
        have := norm_le_norm_sub_add z c
        linarith
      calc B * (q : ℝ) ^ 5 * (‖z‖ + 2) ^ 5 ≤ B * (q : ℝ) ^ 5 * (4 * (|t| + 2)) ^ 5 := by gcongr
        _ = _ := by rw [hX]; ring)
  have e : (4 / 5 : ℝ) * (15 / 4) = 3 := by norm_num
  rw [e] at h1 h2 h3
  have hlog : Real.log (1024 * B * X ^ 5 / ‖F c‖) ≤ Real.log (2048 * B) + 5 * Real.log X := by
    have hX0 : 0 < X := by linarith
    have : 1024 * B * X ^ 5 / ‖F c‖ ≤ 2048 * B * X ^ 5 := by
      rw [div_le_iff₀ hpos]
      have : 0 < B * X ^ 5 := by positivity
      nlinarith
    refine (Real.log_le_log (by positivity) this).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hfin : C * (1 + Real.log (1024 * B * X ^ 5 / ‖F c‖))
      ≤ C * (2 * (1 + |Real.log (2048 * B)|) + 5) * Real.log X := by
    rw [mul_assoc C]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    have h5 := le_abs_self (Real.log (2048 * B))
    have h6 := abs_nonneg (Real.log (2048 * B))
    nlinarith
  set K := C * (2 * (1 + |Real.log (2048 * B)|) + 5) * Real.log X with hK
  have hset : zerosDisc χ c 3 = {w : ℂ | ‖w - c‖ ≤ 3 ∧ F w = 0} := by
    ext w
    simp only [zerosDisc, Set.mem_setOf_eq, f3]
  rw [hset]
  simp only [finsum_mem_eq_finite_toFinset_sum _ h1] at h2 h3 ⊢
  set Z := h1.toFinset with hZ
  have hZm : ∀ w, w ∈ Z ↔ ‖w - c‖ ≤ 3 ∧ F w = 0 := fun w => h1.mem_toFinset
  have hord : ∀ w ∈ Z, analyticOrderNatAt F w = ord χ w := fun w hw => f4 w ((hZm w).1 hw).2
  have hZre : ∀ w ∈ Z, w.re < 1 := fun w hw => by
    obtain ⟨a, b⟩ := (f3 w).1 ((hZm w).1 hw).2
    by_contra hh
    exact LFunction_ne_zero_of_one_le_re χ a (not_lt.1 hh) b
  refine ⟨h1, ?_, ?_⟩
  · rw [← Finset.sum_congr rfl fun w hw => congrArg (Nat.cast : ℕ → ℝ) (hord w hw)]
    exact h2.trans hfin
  set g : ℂ → ℂ := fun z => deriv F z / F z - ∑ w ∈ Z, (ord χ w : ℂ) / (z - w) with hg
  have hnz : ∀ z ∈ Metric.ball c (5 / 2) \ (Z : Set ℂ), F z ≠ 0 := fun z hz h0 =>
    hz.2 ((hZm z).2 ⟨by linarith [mem_ball_iff_norm.1 hz.1], h0⟩)
  have hcau := cauchy K (Metric.ball c (5 / 2)) Metric.isOpen_ball Z g
    (fun z hz => by
      refine DifferentiableAt.differentiableWithinAt ?_
      refine ((hF.deriv z).div (hF z) (hnz z hz)).sub (DifferentiableAt.fun_sum fun w hw => ?_)
      exact (differentiableAt_const _).div (differentiableAt_id.sub_const w)
        (sub_ne_zero.2 (by rintro rfl; exact hz.2 hw)))
    (fun z hz => by
      have h4 := (h3 z (by linarith [mem_ball_iff_norm.1 hz.1]) (hnz z hz)).trans hfin
      rw [Finset.sum_congr rfl fun w hw => by rw [hord w hw]] at h4
      exact le_trans (le_mul_of_one_le_left (norm_nonneg _) (by norm_num)) h4)
    s σ (by linarith) (fun h => by linarith [hZre s h])
    (fun z hz => by
      have hsc : ‖s - c‖ = 2 - σ := by
        have : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        ring
      have := norm_sub_le_norm_sub_add_norm_sub z s c
      rw [mem_ball_iff_norm]
      linarith [mem_closedBall_iff_norm.1 hz]) k
  have hit := iter ((fun n : ℕ => χ (n : ZMod q)) * fun n : ℕ => ((Λ n : ℝ) : ℂ))
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      LSeriesSummable_twist_vonMangoldt χ (by simpa using hy))
    (if χ = 1 then 1 else 0) Z (fun w => (ord χ w : ℂ)) (fun w hw => (hZre w hw).le) g
    (fun z hz => by
      rw [LSeries_twist_vonMangoldt_eq χ hz, ← deriv_LFunction_eq_deriv_LSeries χ hz,
        ← LFunction_eq_LSeries χ hz, hg]
      simp only [f5 z hz]
      ring) k s (by rw [hsre]; exact hs1)
  rw [hit, derSeries_eq, ← mul_add, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast, mul_div_assoc] at hcau
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  refine le_trans (le_of_eq ?_) (le_of_mul_le_mul_left hcau hk)
  congr 1
  split_ifs <;> ring

end GlobalTheory.LogDerivHigher
