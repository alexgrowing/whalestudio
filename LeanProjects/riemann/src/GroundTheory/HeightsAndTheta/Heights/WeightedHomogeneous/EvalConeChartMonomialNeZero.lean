import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace BoundedMonomials

def chartNorm (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (e : MvPolynomial (Coord n) ℤ) (z : Cone n ℂ) : ℝ :=
  ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z)

omit [Fintype ι] in

theorem prod_pow_weight [Fintype ι] {F : Type*} [CommRing F] (u : ι → F) (m : Coord n →₀ ℕ) :
    (m.prod fun v e ↦ u v.1 ^ e) = ∏ k, u k ^ Finsupp.weight (coordDeg n) m k := by
  simp only [Finsupp.weight_apply, coordDeg, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finsupp.prod]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [Finset.prod_eq_single v.1 (fun k _ hk ↦ by simp [hk]) (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp

theorem evalCone_scale {F : Type*} [CommRing F] (u : ι → F) (z : Cone n F)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    evalCone (fun k i ↦ u k * z k i) f = (∏ k, u k ^ δ k) * evalCone z f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [evalCone, eval₂_sum, eval₂_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hw : Finsupp.weight (coordDeg n) m = δ := hf (mem_support_iff.mp hm)
  rw [← hw, ← prod_pow_weight u m]
  simp only [mul_pow, Finsupp.prod_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in

theorem continuous_evalCone (f : MvPolynomial (Coord n) ℤ) :
    Continuous fun z : Cone n ℂ ↦ evalCone z f := by
  have h : (fun z : Cone n ℂ ↦ evalCone z f) =
      fun z ↦ eval (fun v : Coord n ↦ z v.1 v.2) (map (Int.castRingHom ℂ) f) := by
    funext z
    rw [eval_map]
    rfl
  rw [h]
  exact (continuous_eval _).comp
    (continuous_pi fun v ↦ (continuous_apply v.2).comp (continuous_apply v.1))

omit [Fintype ι] [DecidableEq ι] in
theorem evalCone_X {F : Type*} [CommRing F] (z : Cone n F) (k : ι) (i : Fin (n k + 1)) :
    evalCone z (X ⟨k, i⟩) = z k i := by
  simp [evalCone]

omit [DecidableEq ι] in
theorem evalCone_chartMonomial' {F : Type*} [CommRing F] (z : Cone n F)
    (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by
  simp [evalCone, chartMonomial, eval₂_prod]

omit [DecidableEq ι] in
theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)} (d : ι → ℕ)
    (hc : ∀ k, z k (c k) ≠ 0) : evalCone z (chartMonomial c d) ≠ 0 := by
  rw [evalCone_chartMonomial']
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

theorem chartNorm_eq {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg) {z : Cone n ℂ}
    (hz : z ∈ P.points ℂ) {c c' : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ} {e e' : MvPolynomial (Coord n) ℤ}
    (he : IsChartForm P A.deg s.num s.den c d e) (he' : IsChartForm P A.deg s.num s.den c' d' e')
    (hc : ∀ k, z k (c k) ≠ 0) (hc' : ∀ k, z k (c' k) ≠ 0) :
    chartNorm A c d e z = chartNorm A c' d' e' z := by
  set m := chartMonomial c d
  set m' := chartMonomial c' d'
  have hmem : e * m' - e' * m ∈ P.ideal := by
    have h : s.den * (e * m' - e' * m) =
        (s.den * e - s.num * m) * m' - (s.den * e' - s.num * m') * m := by ring
    have h2 : s.den * (e * m' - e' * m) ∈ P.ideal := by
      rw [h]
      exact P.ideal.sub_mem (P.ideal.mul_mem_right _ he.2) (P.ideal.mul_mem_right _ he'.2)
    exact (P.isPrime.mem_or_mem h2).resolve_left s.den_not_mem
  have h0 : evalCone z (e * m' - e' * m) = 0 := hz.2 _ hmem
  simp only [evalCone, eval₂_sub, eval₂_mul, sub_eq_zero] at h0
  have hn : ‖evalCone z e‖ * ‖evalCone z m'‖ = ‖evalCone z e'‖ * ‖evalCone z m‖ := by
    rw [← norm_mul, ← norm_mul]
    exact congrArg norm h0
  have hh : 0 < A.metric z := A.metric_pos z hz.1
  have hm : ‖evalCone z m‖ ≠ 0 := norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d hc)
  have hm' : ‖evalCone z m'‖ ≠ 0 := norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d' hc')
  unfold chartNorm
  rw [div_eq_div_iff (mul_ne_zero hm hh.ne') (mul_ne_zero hm' hh.ne')]
  calc ‖evalCone z e‖ * (‖evalCone z m'‖ * A.metric z)
      = (‖evalCone z e‖ * ‖evalCone z m'‖) * A.metric z := by ring
    _ = (‖evalCone z e'‖ * ‖evalCone z m‖) * A.metric z := by rw [hn]
    _ = ‖evalCone z e'‖ * (‖evalCone z m‖ * A.metric z) := by ring

theorem chartNorm_scale (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    {e : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (he : IsWeightedHomogeneous (coordDeg n) e δ)
    (hδ : ∀ k, (δ k : ℤ) = A.deg k + d k) {u : ι → ℂ} (hu : ∀ k, u k ≠ 0) {z : Cone n ℂ}
    (hz : BlockNonzero z) :
    chartNorm A c d e (fun k i ↦ u k * z k i) = chartNorm A c d e z := by
  unfold chartNorm
  rw [evalCone_scale u z he, evalCone_scale u z (isWeightedHomogeneous_chartMonomial c d),
    A.metric_smul u z hu hz, norm_mul, norm_mul, norm_prod, norm_prod]
  simp only [norm_pow]
  have hQ : ∏ k, ‖u k‖ ^ δ k = (∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    have hk : ‖u k‖ ≠ 0 := norm_ne_zero_iff.mpr (hu k)
    rw [← zpow_natCast, ← zpow_natCast, hδ k, zpow_add₀ hk, mul_comm]
  have hD : (∏ k, ‖u k‖ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))
  have hH : (∏ k, ‖u k‖ ^ A.deg k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))
  rw [hQ]
  have h : (∏ k, ‖u k‖ ^ d k) * ‖evalCone z (chartMonomial c d)‖ *
      ((∏ k, ‖u k‖ ^ A.deg k) * A.metric z) =
      ((∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k) *
        (‖evalCone z (chartMonomial c d)‖ * A.metric z) := by ring
  rw [h, mul_div_mul_left _ _ (mul_ne_zero hD hH)]

def unitChart (c : (k : ι) → Fin (n k + 1)) : Set (Cone n ℂ) :=
  {z | (∀ k, z k (c k) = 1) ∧ ∀ k i, ‖z k i‖ ≤ 1}

omit [DecidableEq ι] in
theorem isCompact_unitChart (c : (k : ι) → Fin (n k + 1)) : IsCompact (unitChart c) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h : unitChart c = (⋂ k, {z : Cone n ℂ | z k (c k) = 1}) ∩
        ⋂ k, ⋂ i, {z : Cone n ℂ | ‖z k i‖ ≤ 1} := by
      ext z
      simp [unitChart]
    rw [h]
    refine (isClosed_iInter fun k ↦ ?_).inter (isClosed_iInter fun k ↦ isClosed_iInter fun i ↦ ?_)
    · exact isClosed_eq ((continuous_apply (c k)).comp (continuous_apply k)) continuous_const
    · exact isClosed_le ((continuous_apply i).comp (continuous_apply k)).norm continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Cone n ℂ)) (r := 1)).subset fun z hz ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    exact hz.2 k

omit [DecidableEq ι] in

theorem exists_bound_unitChart (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (e : MvPolynomial (Coord n) ℤ) : ∃ B : ℝ, ∀ z ∈ unitChart c, chartNorm A c d e z ≤ B := by
  have hnz : ∀ z ∈ unitChart c, BlockNonzero z := fun z hz k h0 ↦ by
    have := hz.1 k
    rw [h0] at this
    exact zero_ne_one this
  have hcont : ContinuousOn (chartNorm A c d e) (unitChart c) := by
    refine ContinuousOn.div (continuous_evalCone e).norm.continuousOn
      (((continuous_evalCone _).norm.continuousOn).mul
        (A.metric_smooth.continuousOn.mono fun z hz ↦ hnz z hz)) fun z hz ↦ ?_
    refine mul_ne_zero (norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d fun k ↦ ?_))
      (A.metric_pos z (hnz z hz)).ne'
    rw [hz.1 k]
    exact one_ne_zero
  obtain ⟨B, hB⟩ := (isCompact_unitChart c).exists_bound_of_continuousOn hcont
  exact ⟨B, fun z hz ↦ (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z hz))⟩

theorem exists_bound_chart {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg)
    (c : (k : ι) → Fin (n k + 1)) :
    ∃ B : ℝ, ∀ z ∈ P.points ℂ, (∀ k, z k (c k) ≠ 0) → (∀ k i, ‖z k i‖ ≤ ‖z k (c k)‖) →
      ∀ (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsChartForm P A.deg s.num s.den c d e →
        chartNorm A c d e z ≤ B := by
  by_cases hlive : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal
  · obtain ⟨d₀, e₀, he₀⟩ := s.regular c hlive
    obtain ⟨B, hB⟩ := exists_bound_unitChart A c d₀ e₀
    refine ⟨B, fun z hz hc hmax d e he ↦ ?_⟩
    obtain ⟨δ, hδe, hδ⟩ := he₀.1
    set u : ι → ℂ := fun k ↦ (z k (c k))⁻¹
    have hu : ∀ k, u k ≠ 0 := fun k ↦ inv_ne_zero (hc k)
    rw [chartNorm_eq s hz he he₀ hc hc, ← chartNorm_scale A c d₀ hδe hδ hu hz.1]
    refine hB _ ⟨fun k ↦ inv_mul_cancel₀ (hc k), fun k i ↦ ?_⟩
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr (hc k)), mul_one]
    exact hmax k i
  · refine ⟨0, fun z hz hc _ d e _ ↦ ?_⟩
    simp only [not_forall, not_not] at hlive
    obtain ⟨k, hk⟩ := hlive
    have h0 := hz.2 _ hk
    rw [evalCone_X] at h0
    exact absurd h0 (hc k)

theorem proof : BoundedMonomials.Statement := by
  intro ι _ _ n P A s
  refine ⟨fun z hz c c' d d' e e' he he' hc hc' ↦ chartNorm_eq s hz he he' hc hc', ?_⟩
  choose B hB using exists_bound_chart s
  refine ⟨Real.log (∑ c, |B c| + 1), fun z hz c d e he hc ↦ ?_⟩
  have hS : 0 < ∑ c, |B c| + 1 := by positivity
  rw [Real.exp_log hS]

  have hmax : ∀ k, ∃ i, ∀ j, ‖z k j‖ ≤ ‖z k i‖ := fun k ↦ by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j ↦ ‖z k j‖) Finset.univ_nonempty
    exact ⟨i, fun j ↦ hi j (Finset.mem_univ j)⟩
  choose c₀ hc₀ using hmax
  have hc₀z : ∀ k, z k (c₀ k) ≠ 0 := fun k h0 ↦ by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hz.1 k)
    have := hc₀ k j
    rw [h0, norm_zero] at this
    exact hj (norm_le_zero_iff.mp this)
  have hlive : ∀ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦ by
    have h0 := hz.2 _ hk
    rw [evalCone_X] at h0
    exact hc₀z k h0
  obtain ⟨d₀, e₀, he₀⟩ := s.regular c₀ hlive
  change chartNorm A c d e z ≤ _
  rw [chartNorm_eq s hz he he₀ hc hc₀z]
  calc chartNorm A c₀ d₀ e₀ z ≤ B c₀ := hB c₀ z hz hc₀z hc₀ d₀ e₀ he₀
    _ ≤ |B c₀| := le_abs_self _
    _ ≤ ∑ c, |B c| := Finset.single_le_sum (fun c _ ↦ abs_nonneg (B c)) (Finset.mem_univ c₀)
    _ ≤ ∑ c, |B c| + 1 := by linarith

end BoundedMonomials

end

end GroundTheory.Heights₂.Heights
