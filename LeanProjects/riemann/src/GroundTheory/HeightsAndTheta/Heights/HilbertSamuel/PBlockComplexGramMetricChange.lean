import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMetricPair
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionFormsIndependent
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory Filter
  Asymptotics
open scoped ComplexConjugate Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockComplexGramMetricChange

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem eval_torus {F : MvPolynomial (Σ k, ι k) ℂ} {k₀ : K} {n : ℕ} (hF : IsMultiHomog F (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) F = c k₀ ^ n * eval z F := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hF m hm
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem isMultiHomog_mapQ {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (map (Int.castRingHom ℚ) f) a := fun m hm => hf m (support_map_subset _ _ hm)

theorem isMultiHomog_mapC {b : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ} (hb : IsMultiHomog b a) :
    IsMultiHomog (map (algebraMap ℚ ℂ) b) a := fun m hm => hb m (support_map_subset _ _ hm)

theorem prod_norm_unitDeg (c : K → ℂ) (k₀ : K) : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
  rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
  simp [unitDeg]

theorem h_torus (B : HermLine ι) {k₀ : K} (hB : B.a = unitDeg k₀) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : B.h (fun p => c p.1 * z p) = ‖c k₀‖ * B.h z := by
  rw [B.smul c z hc, hB, prod_norm_unitDeg]

theorem blockPt_mem (d : HSMBlockDatum D K ι Ω) (y : d.R.X) : ∀ k, ∃ i, blockPt d y ⟨k, i⟩ ≠ 0 :=
  (d.R.mem y y (d.R.mem_U y)).1

theorem pair_torus (B : HermLine ι) {k₀ : K} (hB : B.a = unitDeg k₀) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {n : ℕ}
    {b b' : MvPolynomial (Σ k, ι k) ℚ} (hb : IsMultiHomog b (blockDeg k₀ n))
    (hb' : IsMultiHomog b' (blockDeg k₀ n)) :
    eval (fun p => c p.1 * z p) (map (algebraMap ℚ ℂ) b) *
        conj (eval (fun p => c p.1 * z p) (map (algebraMap ℚ ℂ) b')) *
        ((Real.exp (-(n : ℝ) * (2 * Real.log (B.h (fun p => c p.1 * z p)))) : ℝ) : ℂ) =
      pairValH B n b b' z := by
  have hρ : 0 < B.h z := B.pos z hz
  have hcn : 0 < ‖c k₀‖ := norm_pos_iff.2 (hc k₀)
  have hexp : Real.exp (-(n : ℝ) * (2 * Real.log (B.h (fun p => c p.1 * z p)))) =
      ((‖c k₀‖ * B.h z) ^ (2 * n))⁻¹ := by
    rw [h_torus B hB c hc, show -(n : ℝ) * (2 * Real.log (‖c k₀‖ * B.h z)) =
      -(((2 * n : ℕ) : ℝ) * Real.log (‖c k₀‖ * B.h z)) by push_cast; ring, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (mul_pos hcn hρ)]
  have hcc : c k₀ ^ n * conj (c k₀) ^ n = ((‖c k₀‖ : ℝ) : ℂ) ^ (2 * n) := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    ring
  rw [hexp, eval_torus (isMultiHomog_mapC hb), eval_torus (isMultiHomog_mapC hb'), pairValH]
  have hρc : ((B.h z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hcc' : ((‖c k₀‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcn.ne'
  simp only [map_mul, map_pow]
  push_cast
  field_simp
  linear_combination (eval z (map (algebraMap ℚ ℂ) b) * conj (eval z (map (algebraMap ℚ ℂ) b')) *
    ((B.h z : ℝ) : ℂ) ^ (2 * n)) * hcc

theorem continuous_diff {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
    (W₁ W₀ : Weight L) : Continuous (Weight.diff W₁ W₀) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  set j := chartIdx A x
  have hT : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target :=
    Set.inter_eq_left.2 fun y hy => (A.chart j).map_target hy
  have h₁ := (W₁.smooth j j).continuousOn
  have h₀ := (W₀.smooth j j).continuousOn
  rw [hT] at h₁ h₀
  have hg := (h₁.sub h₀).continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hx))
  refine (hg.comp ((A.chart j).continuousAt hx)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  simp only [Pi.sub_apply, Function.comp_apply, (A.chart j).left_inv hy]
  exact (Weight.diff_eq W₁ W₀ j hy).symm

theorem eventually_pow_le (C ε : ℝ) (hε : 0 < ε) (hD : 1 ≤ D) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) + 1) ^ (D - 1) ≤ ε * (n : ℝ) ^ D := by
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨N, hN⟩ := exists_nat_ge (|C| * 2 ^ D' / ε)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hkey : |C| * 2 ^ D' ≤ ε * n := by
    have := hN.trans hnN
    rw [div_le_iff₀ hε] at this
    linarith
  calc C * ((n : ℝ) + 1) ^ D' ≤ |C| * ((n : ℝ) + 1) ^ D' :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 * (n : ℝ)) ^ D' :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (abs_nonneg C)
    _ = (|C| * 2 ^ D') * (n : ℝ) ^ D' := by rw [mul_pow]; ring
    _ ≤ (ε * n) * (n : ℝ) ^ D' := mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = ε * (n : ℝ) ^ (D' + 1) := by ring

end BlockComplexGramMetricChange

open BlockComplexGramMetricChange in

theorem BlockComplexGramMetricChange.proof (hMC : MetricChange.Statement)
    (hPair : BlockResolutionMetricPair.Statement) (hInd : BlockResolutionFormsIndependent.Statement)
    (hDeg : BlockResolutionDegree.Statement) : BlockComplexGramMetricChange.Statement := by
  classical
  intro D K _ _ ι _ Ω _ _ d A' P0' hdeg hc hle hp
  obtain ⟨A, L, W₀, W₁, dV, σ, -, hW₀, hW₁, hμ, hsec, hval, hdens⟩ := hPair D K ι Ω d A' P0' hdeg hle hp
  choose c hc0 hσ hφ₀ hφ₁ using hval

  have hex : ∀ n, ∃ q : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d.y d.k₀ n q.2 :=
    fun n => SupBoundCount.exists_isSecBasisM d.y d.k₀ n
  let p : ℕ → (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ) := fun n => (hex n).choose
  have hp' : ∀ n, IsSecBasisM d.y d.k₀ n (p n).2 := fun n => (hex n).choose_spec
  have hhom : ∀ n k, IsMultiHomog ((p n).2 k) (blockDeg d.k₀ n) := fun n k => by
    obtain ⟨f, hf, hfe⟩ := (hp' n).1 k
    rw [hfe]
    exact isMultiHomog_mapQ hf
  let v : ∀ n, Fin (p n).1 → Fin A.n → d.R.X → ℂ := fun n k => σ n ((p n).2 k)
  have hli : ∀ n, LinearIndependent ℂ (v n) := by
    intro n
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g = 0 := hInd D K ι Ω d n _ (p n).2 (hp' n) g fun y => by
      have h := congrFun (congrFun hg (chartIdx A y)) y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v,
        hσ y n _ (hhom n _), eval_torus (isMultiHomog_mapC (hhom n _))] at h
      have hcn : c y d.k₀ ^ n ≠ 0 := pow_ne_zero _ (hc0 y d.k₀)
      apply (mul_right_inj' hcn).1
      rw [mul_zero, Finset.mul_sum, ← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    intro k
    rw [h0]
    rfl
  let V : ℕ → Submodule ℂ (Fin A.n → d.R.X → ℂ) := fun n => Submodule.span ℂ (Set.range (v n))
  have : ∀ n, FiniteDimensional ℂ (V n) := fun n => FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hrank : ∀ n, Module.finrank ℂ (V n) = (p n).1 := fun n =>
    (finrank_span_eq_card (hli n)).trans (Fintype.card_fin _)
  let eB : ∀ n, Module.Basis (Fin (Module.finrank ℂ (V n))) ℂ (V n) := fun n =>
    (Module.Basis.span (hli n)).reindex (finCongr (hrank n).symm)

  have hgram : ∀ (W : Weight L) (B : HermLine ι), B.a = unitDeg d.k₀ →
      (∀ y, W.φ (chartIdx A y) y = 2 * Real.log (B.h (fun q => c y q.1 * blockPt d y q))) → ∀ n,
      chiGram W dV n (fun a => ((eB n a : V n) : Fin A.n → d.R.X → ℂ)) =
        -(1 / 2) * Real.log (Matrix.det (fun k l => ∫ y, pairValH B n ((p n).2 k) ((p n).2 l) (blockPt d y) ∂d.dV :
          Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re := by
    intro W B hB hW n
    have he : (fun a => ((eB n a : V n) : Fin A.n → d.R.X → ℂ)) =
        fun a => v n ((finCongr (hrank n).symm).symm a) := by
      funext a
      simp only [eB, Module.Basis.reindex_apply, Module.Basis.span_apply]
    have hsub : gram W dV n (fun a => v n ((finCongr (hrank n).symm).symm a)) =
        (gram W dV n (v n)).submatrix (finCongr (hrank n).symm).symm (finCongr (hrank n).symm).symm := by
      ext a a'
      rfl
    have hg : gram W dV n (v n) = fun k l => ∫ y, pairValH B n ((p n).2 k) ((p n).2 l) (blockPt d y) ∂d.dV := by
      ext k l
      simp only [gram, Matrix.of_apply, hμ, v]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      rw [hσ y n _ (hhom n k), hσ y n _ (hhom n l), hW y]
      exact pair_torus B hB (blockPt_mem d y) (hc0 y) (hhom n k) (hhom n l)
    rw [chiGram, he, hsub, Matrix.det_submatrix_equiv_self, hg]
  have hC₀ : ∀ n, blockCChi d n = -(1 / 2) * Real.log (Matrix.det (fun k l =>
      ∫ y, pairValH d.A n ((p n).2 k) ((p n).2 l) (blockPt d y) ∂d.dV :
        Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re := fun n => by
    rw [blockCChi, dif_pos (hex n)]
    rfl
  have hC₁ : ∀ n, blockCChi (d.withMetric A' P0' hdeg hc hle hp) n = -(1 / 2) * Real.log (Matrix.det (fun k l =>
      ∫ y, pairValH A' n ((p n).2 k) ((p n).2 l) (blockPt d y) ∂d.dV :
        Matrix (Fin (p n).1) (Fin (p n).1) ℂ)).re := fun n => by
    rw [blockCChi, dif_pos (show ∃ q : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ),
      IsSecBasisM (d.withMetric A' P0' hdeg hc hle hp).y (d.withMetric A' P0' hdeg hc hle hp).k₀ n q.2 from hex n)]
    rfl

  have hdim : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (∫ y, bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ - ε) * (n : ℝ) ^ D ≤ Module.finrank ℂ (V n) := by
    intro t ht ε hε
    obtain ⟨C, hr⟩ := hDeg D K ι Ω d d.A A' d.deg hdeg d.semipos.1 hp.1 t ht
    have hI := hdens t ht (fun _ => 1) continuous_const
    simp only [one_mul] at hI
    rw [hI]
    filter_upwards [eventually_pow_le C ε hε d.one_le] with n hn
    rw [hrank n, ← SupBoundCount.finrank_secM (hp' n)]
    have h := (abs_le.1 (hr n)).1
    set δ := mInt d.R.A (fun _ => blockInterpPot d d.A A' t) fun _ => 1
    have e1 : (δ / (D.factorial : ℝ) - ε) * (n : ℝ) ^ D =
        δ * (n : ℝ) ^ D / (D.factorial : ℝ) - ε * (n : ℝ) ^ D := by ring
    rw [e1]
    linarith
  have hVle : ∀ n, V n ≤ L.sections n := fun n =>
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hsec n _ (hhom n k))
  have hM := hMC A L W₀ W₁ dV hW₀ hW₁ V hVle hdim eB

  have hdiff : ∀ y, Weight.diff W₁ W₀ y = 2 * Real.log (A'.h (blockPt d y) / d.A.h (blockPt d y)) := by
    intro y
    have hz := blockPt_mem d y
    have hcn : ‖c y d.k₀‖ ≠ 0 := norm_ne_zero_iff.2 (hc0 y d.k₀)
    rw [Weight.diff, hφ₁ y, hφ₀ y, h_torus A' hdeg _ (hc0 y), h_torus d.A d.deg _ (hc0 y),
      Real.log_mul hcn (A'.pos _ hz).ne', Real.log_mul hcn (d.A.pos _ hz).ne',
      Real.log_div (A'.pos _ hz).ne' (d.A.pos _ hz).ne']
    ring
  have hcont : Continuous fun y => Real.log (A'.h (blockPt d y) / d.A.h (blockPt d y)) := by
    have h : (fun y => Real.log (A'.h (blockPt d y) / d.A.h (blockPt d y))) =
        fun y => Weight.diff W₁ W₀ y / 2 := by
      funext y
      rw [hdiff]
      ring
    rw [h]
    exact (continuous_diff W₁ W₀).div_const 2
  have hK : ∫ t in (0 : ℝ)..1, ∫ y, Weight.diff W₁ W₀ y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
      2 / (D.factorial : ℝ) * blockMetricInt d A' := by
    rw [blockMetricInt, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only [hdiff]
    have h := hdens t ht _ hcont
    simp only [mul_assoc]
    rw [integral_const_mul, h]
    ring

  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [hM ε hε] with n hn
  rw [hgram W₁ A' hdeg hφ₁ n, hgram W₀ d.A d.deg hφ₀ n, hK] at hn
  rw [hC₁ n, hC₀ n, Real.norm_eq_abs, Real.norm_eq_abs, pw,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))]
  have e2 : (n : ℝ) ^ (D + 1) / 2 * (2 / (D.factorial : ℝ) * blockMetricInt d A') =
      (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * blockMetricInt d A' := by ring
  rw [e2] at hn
  exact hn

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
