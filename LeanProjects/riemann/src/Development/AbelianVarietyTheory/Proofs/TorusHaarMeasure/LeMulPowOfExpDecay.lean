import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem le_mul_pow_of_exp_decay {c c₁ l φ K K' nF s : ℝ} (T : ℕ) (hc : 0 ≤ c₁) (hl : 0 ≤ l)
    (hnF : nF ≤ K * Real.exp (-2 * Real.pi * c₁ / l)) (hK' : Real.exp (-(2 * c * φ)) ≤ K' * s)
    (hp : (T : ℝ) * c * φ ≤ c₁ / l) : nF ≤ max K 0 * K' ^ T * s ^ T := by
  have hq : 0 ≤ c₁ / l := div_nonneg hc hl
  have h1 : Real.exp (-2 * Real.pi * c₁ / l) ≤ Real.exp (-(2 * c * φ)) ^ T := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have e : -2 * Real.pi * c₁ / l = -2 * Real.pi * (c₁ / l) := by ring
    rw [e]
    nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-(2 * c * φ)) ^ T ≤ (K' * s) ^ T :=
    pow_le_pow_left₀ (Real.exp_pos _).le hK' T
  calc nF ≤ K * Real.exp (-2 * Real.pi * c₁ / l) := hnF
    _ ≤ max K 0 * Real.exp (-2 * Real.pi * c₁ / l) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max K 0 * (K' * s) ^ T := mul_le_mul_of_nonneg_left (h1.trans h2) (le_max_right _ _)
    _ = max K 0 * K' ^ T * s ^ T := by rw [mul_pow, mul_assoc]

theorem sum_pnorm_w_sq_pos {r : ℕ} {X : Data E r} (Xa : ArchInM X) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  obtain ⟨K, hK⟩ := Xa.p3
  have h0 : 0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  rcases eq_or_lt_of_le h0 with h | h
  · have h1 := hK x hx
    rw [← h, mul_zero] at h1
    exact absurd h1 (not_le.mpr (Real.exp_pos _))
  · exact h

theorem highModes_le_pow_w : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), ∀ F ∈ X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1,
    (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (Xa.Fp + Xa.T • Xa.L) F x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ Xa.T) ∧
    ∀ x0 FF, IsFundSet X x0 FF → muF X x0 FF < ⊤ →
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) F (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ := by
  intro r X Xa F hF
  obtain ⟨K, hK⟩ := cuspidalDecay_holds r X _ F Xa.c1 Xa.frame_theta_const_pos.le hF
  obtain ⟨K', hK'⟩ := Xa.p3
  have hbd : ∀ x ∈ X.dom, X.pnorm (Xa.Fp + Xa.T • Xa.L) F x ^ 2 ≤
      (max K 0 * K' ^ Xa.T) * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ Xa.T := by
    intro x hx
    have hl := MinimumGrowthBounds.minimumSq_nonneg X hx
    have hp := Xa.p2 x hx
    rw [Data.la1, Real.sq_sqrt hl] at hp
    exact le_mul_pow_of_exp_decay Xa.T Xa.frame_theta_const_pos.le hl (hK x hx) (hK' x hx) hp
  refine ⟨⟨_, hbd⟩, fun x0 FF hFF hfin => ?_⟩
  calc ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) F (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0
      ≤ ∫⁻ _ in FF, ENNReal.ofReal (max K 0 * K' ^ Xa.T) ∂muF X x0 := by
        refine setLIntegral_mono' hFF.1 fun z hz => ENNReal.ofReal_le_ofReal ?_
        have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
        have hs := sum_pnorm_w_sq_pos Xa hx
        rw [Real.rpow_neg hs.le, Real.rpow_natCast, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hs _)]
        exact hbd _ hx
    _ = ENNReal.ofReal (max K 0 * K' ^ Xa.T) * muF X x0 FF := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end GlobalTheory
