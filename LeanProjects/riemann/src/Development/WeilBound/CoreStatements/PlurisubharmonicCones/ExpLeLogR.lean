import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts

open Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm.A (IsPsh coordDiv)
open scoped ContDiff

namespace LevelTowerAlt.Reg

variable {n : ℕ}

theorem usc_comp {U : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (h : UpperSemicontinuousOn φ U)
    {g : (Fin n → ℂ) → Fin n → ℂ} (hg : Continuous g) : UpperSemicontinuousOn (fun t => φ (g t)) (g ⁻¹' U) := by
  intro z hz y hy
  have h1 : ∀ᶠ x in 𝓝[U] (g z), φ x < y := h _ hz y hy
  exact (hg.continuousWithinAt.tendsto_nhdsWithin (Set.mapsTo_preimage g U)).eventually h1

theorem isPsh_aff {U : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (h : IsPsh U φ) (t₀ : Fin n → ℂ) (c : ℂ) :
    IsPsh ((fun t => t₀ + c • t) ⁻¹' U) fun t => φ (t₀ + c • t) := by
  refine ⟨usc_comp h.1 (by fun_prop), fun z w hd => ?_⟩
  have e : ∀ ζ : ℂ, t₀ + c • (z + ζ • w) = t₀ + c • z + ζ • (c • w) := fun ζ => by
    rw [smul_add, smul_comm c ζ, add_assoc]
  simp only [e]
  exact h.2 _ _ fun ζ hζ => e ζ ▸ hd ζ hζ

theorem isPsh_star {U : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (h : IsPsh U φ) :
    IsPsh (star ⁻¹' U) fun t => φ (star t) := by
  refine ⟨usc_comp h.1 continuous_star, fun z w hd => ?_⟩
  have e : ∀ ζ : ℂ, star (z + ζ • w) = star z + star ζ • star w := fun ζ => by rw [star_add, star_smul]
  obtain ⟨h1, h2⟩ := h.2 (star z) (star w) fun ζ hζ => by
    have := hd (star ζ) (by rwa [norm_star])
    rwa [Set.mem_preimage, e, star_star] at this
  have hc : ∀ θ : ℝ, star (circleMap 0 1 θ) = circleMap 0 1 (2 * Real.pi - θ) := fun θ => by
    rw [sub_eq_add_neg, add_comm, periodic_circleMap]
    simp [circleMap, ← Complex.exp_conj]
  refine ⟨?_, h2.trans_eq ?_⟩
  · unfold CircleIntegrable at h1 ⊢
    simp only [e, hc]
    have := (h1.comp_sub_left (2 * Real.pi)).symm
    simpa using this
  · unfold Real.circleAverage
    simp only [e, hc]
    rw [intervalIntegral.integral_comp_sub_left (fun θ => φ (star z + circleMap 0 1 θ • star w))]
    simp

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}
  {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd)

theorem exp_le_logR {t : Fin n → ℂ} (ht : ‖t‖ < 1) : Real.exp 1 ≤ χ.logR t := by
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => ?_)
  split_ifs
  · rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm t i).trans ht.le))
  · exact le_rfl

theorem piece {F : (Fin n → ℂ) → ℝ} (hO : IsOpen {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd})
    (hFs : ContDiffOn ℝ ∞ F {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd})
    (hFp : IsPsh {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd} F) {t₀ : Fin n → ℂ} {ε C Q : ℝ}
    (h₀ : ‖t₀‖ ≤ 1 / 2) (hε : 0 < ε) (hε' : ε ≤ 1 / 4) (hsep : ∀ i, t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖) (hC : 0 < C)
    (hb : ∀ t ∈ {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd}, ‖t - t₀‖ < 2 * ε →
      -(C * Real.log (χ.logR t)) ≤ F t ∧ F t ≤ C ∧
        ‖fderiv ℝ F t‖ ≤ C * χ.logR t ^ C * Real.exp (χ.logR t / 2))
    (L : (Fin n → ℂ) →L[ℝ] Fin n → ℂ) (hL : ∀ t i, ‖L t i‖ = ‖t i‖)
    (hLp : ∀ U φ, IsPsh U φ → IsPsh (L ⁻¹' U) fun t => φ (L t))
    {S : Finset (Fin n)} (hS : ∀ i, i ∈ S ↔ (i : ℕ) < χ.a ∧ t₀ i = 0) {q p : (Fin n → ℂ) → ℝ}
    (hq : ∀ t ∈ ball (0 : Fin n → ℂ) 1, |q t| ≤ Q)
    (hu : ∀ t ∈ ball (0 : Fin n → ℂ) 1, χ.γ (t₀ + (ε : ℂ) • L t) ∉ Bd → q t + p t = F (t₀ + (ε : ℂ) • L t)) :
    ContDiffOn ℝ ∞ (fun y => q y + p y) (ball 0 1 \ coordDiv S) ∧
      IsPsh (ball 0 1 \ coordDiv S) (fun y => q y + p y) ∧
      ∃ C' c : ℝ, 0 < C' ∧ ∀ t ∈ ball (0 : Fin n → ℂ) 1 \ coordDiv S, ∀ ρ : ℝ,
        Real.exp 1 + c + ∑ i ∈ S, Real.log (‖t i‖ ^ 2)⁻¹ ≤ ρ →
          p t ≤ C' ∧ -C' * Real.log ρ ≤ p t ∧
            ‖fderiv ℝ (fun y => q y + p y) t‖ ≤ C' * ρ ^ C' * Real.exp (ρ / 2) := by
  classical
  set O := {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd} with hOdef
  have hLn : ∀ t, ‖L t‖ ≤ ‖t‖ := fun t =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (hL t i).trans_le (norm_le_pi_norm t i)
  have hεn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_of_nonneg hε.le]
  have hT : ∀ t, ‖(ε : ℂ) • L t‖ ≤ ε * ‖t‖ := fun t => by
    rw [norm_smul, hεn]; exact mul_le_mul_of_nonneg_left (hLn t) hε.le
  have hTi : ∀ t i, ‖((ε : ℂ) • L t) i‖ = ε * ‖t i‖ := fun t i => by
    rw [Pi.smul_apply, norm_smul, hεn, hL]
  have hlow : ∀ t : Fin n → ℂ, ‖t‖ < 1 → ∀ i, t₀ i ≠ 0 → ε ≤ ‖(t₀ + (ε : ℂ) • L t) i‖ := fun t ht i hi => by
    have h1 := hsep i hi
    have h2 := hTi t i
    have h3 := norm_sub_le ((t₀ + (ε : ℂ) • L t) i) (((ε : ℂ) • L t) i)
    rw [Pi.add_apply, add_sub_cancel_right] at h3
    rw [Pi.add_apply]
    nlinarith [norm_le_pi_norm t i]
  have hball : ∀ t : Fin n → ℂ, ‖t‖ < 1 → ‖t₀ + (ε : ℂ) • L t‖ < 1 := fun t ht => by
    have := norm_add_le t₀ ((ε : ℂ) • L t)
    nlinarith [hT t, norm_nonneg t]
  have hmap : ∀ t ∈ ball (0 : Fin n → ℂ) 1 \ coordDiv S, t₀ + (ε : ℂ) • L t ∈ O := by
    rintro t ⟨ht, htS⟩
    rw [mem_ball_zero_iff] at ht
    have hb' := mem_ball_zero_iff.2 (hball t ht)
    refine ⟨hb', fun h => ?_⟩
    obtain ⟨i, hi, h0⟩ := (χ.boundary _ hb').1 h
    by_cases h1 : t₀ i = 0
    · refine htS ⟨i, (hS i).2 ⟨hi, h1⟩, ?_⟩
      have h2 := hTi t i
      rw [Pi.add_apply, h1, zero_add] at h0
      rw [h0, norm_zero] at h2
      exact norm_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_left hε.ne')
    · have := hlow t ht i h1
      rw [h0, norm_zero] at this
      linarith
  have hV : IsOpen (ball (0 : Fin n → ℂ) 1 \ coordDiv S) :=
    isOpen_ball.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have heq : Set.EqOn (fun t => F (t₀ + (ε : ℂ) • L t)) (fun y => q y + p y) (ball 0 1 \ coordDiv S) :=
    fun t ht => (hu t ht.1 (hmap t ht).2).symm
  have hσ : ContDiff ℝ ∞ fun t => t₀ + (ε : ℂ) • L t := contDiff_const.add (L.contDiff.const_smul _)
  refine ⟨(hFs.comp hσ.contDiffOn hmap).congr fun t ht => (heq ht).symm,
    GroundTheory.Heights₂.Heights.Regular.isPsh_congr heq ?_, C + |Q|, n * Real.log (1 / ε ^ 2), by positivity,
    fun t ht ρ hρ => ?_⟩
  · have h := hLp _ _ (isPsh_aff hFp t₀ ε)
    exact ⟨h.1.mono hmap, fun z w hd => h.2 z w fun ζ hζ => hmap _ (hd ζ hζ)⟩
  have ht1 : ‖t‖ < 1 := mem_ball_zero_iff.1 ht.1
  set s := t₀ + (ε : ℂ) • L t with hs
  have hsO : s ∈ O := hmap t ht
  obtain ⟨b1, b2, b3⟩ := hb s hsO (by
    rw [hs, add_sub_cancel_left]
    nlinarith [hT t, norm_nonneg t])
  have hRe := exp_le_logR χ (hball t ht1)
  have hRρ : χ.logR s ≤ ρ := by
    refine le_trans ?_ hρ
    have hl0 : 0 ≤ Real.log (1 / ε ^ 2) := Real.log_nonneg (by
      rw [le_div_iff₀ (by positivity)]; nlinarith)
    have : ∑ i : Fin n, (if (i : ℕ) < χ.a then Real.log (1 / ‖s i‖ ^ 2) else 0) ≤
        ∑ i : Fin n, (Real.log (1 / ε ^ 2) + if i ∈ S then Real.log (‖t i‖ ^ 2)⁻¹ else 0) := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : (i : ℕ) < χ.a
      · by_cases h1 : t₀ i = 0
        · have hiS := (hS i).2 ⟨hi, h1⟩
          have hti : ‖t i‖ ≠ 0 := norm_ne_zero_iff.2 fun h => ht.2 ⟨i, hiS, h⟩
          rw [if_pos hi, if_pos hiS, hs, Pi.add_apply, h1, zero_add, hTi,
            ← Real.log_mul (by positivity) (by positivity)]
          refine le_of_eq (congrArg _ ?_)
          field_simp
        · rw [if_pos hi, if_neg fun h => h1 ((hS i).1 h).2, add_zero]
          have h2 := hlow t ht1 i h1
          have h3 : 0 < ‖s i‖ := hε.trans_le h2
          exact Real.log_le_log (by positivity)
            (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hε.le h2 2))
      · rw [if_neg hi, if_neg fun h => hi ((hS i).1 h).1, add_zero]
        exact hl0
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_mem, Finset.univ_inter] at this
    unfold SncChart.logR
    linarith
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hl1 : 1 ≤ Real.log ρ := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have hl2 : Real.log (χ.logR s) ≤ Real.log ρ := Real.log_le_log (by linarith) hRρ
  have hqt := abs_le.1 ((hq t ht.1).trans (le_abs_self Q))
  have hut : q t + p t = F s := hu t ht.1 hsO.2
  refine ⟨by linarith, by nlinarith [abs_nonneg Q], ?_⟩
  have hFd : HasFDerivAt F (fderiv ℝ F s) s :=
    ((hFs.contDiffAt (hO.mem_nhds hsO)).differentiableAt (by simp)).hasFDerivAt
  have hσd : HasFDerivAt (fun t => t₀ + (ε : ℂ) • L t) ((ε : ℂ) • L) t :=
    (L.hasFDerivAt.const_smul (ε : ℂ)).const_add t₀
  have hd : HasFDerivAt (fun y => q y + p y) ((fderiv ℝ F s).comp ((ε : ℂ) • L)) t :=
    (hFd.comp t hσd).congr_of_eventuallyEq
      (by filter_upwards [hV.mem_nhds ht] with y hy using (heq hy).symm)
  rw [hd.fderiv]
  have hn : ‖(fderiv ℝ F s).comp ((ε : ℂ) • L)‖ ≤ ‖fderiv ℝ F s‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    refine ((fderiv ℝ F s).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (hT v).trans ?_
    nlinarith [norm_nonneg v]
  refine hn.trans (b3.trans ?_)
  have hp : χ.logR s ^ C ≤ ρ ^ (C + |Q|) :=
    (Real.rpow_le_rpow (by linarith) hRρ hC.le).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_add_of_nonneg_right (abs_nonneg Q)))
  have hρ0 : 0 ≤ χ.logR s := by linarith
  have hρ1 : 0 ≤ ρ := by linarith
  have hC' : C ≤ C + |Q| := le_add_of_nonneg_right (abs_nonneg Q)
  exact mul_le_mul (mul_le_mul hC' hp (Real.rpow_nonneg hρ0 _) (by positivity))
    (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by positivity)

end LevelTowerAlt.Reg
