import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff

namespace GlobalTheory.RowChoice

theorem per_single_inl {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : Fin g) :
    per τ (Pi.single (Sum.inl k) (1 : ℝ)) = fun j => τ k j := by
  classical
  ext j
  simp [per, vecMul, dotProduct, Pi.single_apply, apply_ite Complex.ofReal, ite_mul]

theorem norm_ch_row {g : ℕ} (n : Fin g → ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) (k : Fin g) :
    ‖ch n (fun j => τ k j)‖ = Real.exp (-(2 * π * ∑ j, (τ k j).im * (n j : ℝ))) := by
  rw [ch, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.re_sum, Complex.im_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem le_norm_sub_one {e : ℂ} {s c : ℝ} (he : ‖e‖ = Real.exp (-(2 * π * s)))
    (hs : c ≤ |s|) : 1 - Real.exp (-(2 * π * c)) ≤ ‖e - 1‖ := by
  have h1 : |‖e‖ - ‖(1 : ℂ)‖| ≤ ‖e - 1‖ := abs_norm_sub_norm_le e 1
  rw [norm_one] at h1
  rcases le_abs'.mp hs with h | h
  · have h3 : 2 * π * c ≤ ‖e‖ - 1 := by
      rw [he]
      have := Real.add_one_le_exp (-(2 * π * s))
      nlinarith [Real.pi_pos]
    have h2 : 1 - Real.exp (-(2 * π * c)) ≤ 2 * π * c := by
      linarith [Real.add_one_le_exp (-(2 * π * c))]
    linarith [le_abs_self (‖e‖ - 1)]
  · have h3 : ‖e‖ ≤ Real.exp (-(2 * π * c)) := by
      rw [he]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith [neg_abs_le (‖e‖ - 1)]

theorem exists_le_norm_mulVec {g : ℕ} {Ω : Matrix (Fin g) (Fin g) ℂ} (h : IsSiegel Ω) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Fin g → ℝ, ‖x‖ ≤ K * ‖Ω.map Complex.im *ᵥ x‖ := by
  have hinj : Function.Injective (Matrix.toLin' (Ω.map Complex.im)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have := h.dotProduct_pos hne
    rw [Matrix.toLin'_apply] at hx
    rw [hx, dotProduct_zero] at this
    exact lt_irrefl _ this
  obtain ⟨K, hK, hA⟩ := (LinearMap.injective_iff_antilipschitz (Matrix.toLin' (Ω.map Complex.im))).mp hinj
  refine ⟨K, NNReal.coe_pos.mpr hK, fun x => ?_⟩
  have := hA.le_mul_dist x 0
  simpa [dist_zero_right, Matrix.toLin'_apply] using this

theorem rowChoice : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ b₀ ∈ U, ∃ V : Set E, IsOpen V ∧ b₀ ∈ V ∧
    V ⊆ U ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ n : Fin g → ℤ, n ≠ 0 → ∃ k : Fin g, ∀ b ∈ V,
    δ ≤ ‖ch n (per (τ b) (Pi.single (Sum.inl k) (1 : ℝ))) - 1‖ := by
  intro g E _ _ U τ hτ b₀ hb₀
  obtain ⟨hU, hdiff, hsieg⟩ := hτ
  obtain ⟨K, hK, hKx⟩ := exists_le_norm_mulVec (hsieg b₀ hb₀)
  set ε : ℝ := 1 / (2 * K * (g + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hev : ∀ᶠ b in nhds b₀, b ∈ U ∧ ∀ k j, |(τ b k j).im - (τ b₀ k j).im| < ε := by
    refine Filter.Eventually.and (hU.mem_nhds hb₀ : ∀ᶠ b in nhds b₀, b ∈ U) ?_
    rw [Filter.eventually_all]; intro k
    rw [Filter.eventually_all]; intro j
    have hc : ContinuousAt (fun b => (τ b k j).im) b₀ :=
      Complex.continuous_im.continuousAt.comp
        ((hdiff k j).differentiableAt (hU.mem_nhds hb₀)).continuousAt
    have := Metric.tendsto_nhds.mp hc ε hεpos
    simpa [Real.dist_eq] using this
  obtain ⟨V, hV, hVo, hb₀V⟩ := eventually_nhds_iff.mp hev
  refine ⟨V, hVo, hb₀V, fun b hb => (hV b hb).1, ?_⟩
  set c : ℝ := 1 / (2 * K) with hc
  have hcpos : 0 < c := by positivity
  refine ⟨1 - Real.exp (-(2 * π * c)),
    sub_pos.mpr ((Real.exp_lt_exp.mpr (neg_neg_of_pos (by positivity))).trans_eq Real.exp_zero), ?_⟩
  intro n hn
  set x : Fin g → ℝ := fun j => (n j : ℝ) with hx
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hn
  have hx1 : 1 ≤ ‖x‖ := by
    have : 1 ≤ |(n i₀ : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi₀
    exact this.trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i₀)
  haveI : Nonempty (Fin g) := ⟨i₀⟩
  obtain ⟨k, hk⟩ := Finite.exists_max (fun k => |((τ b₀).map Complex.im *ᵥ x) k|)
  refine ⟨k, fun b hb => ?_⟩
  set a := ((τ b₀).map Complex.im *ᵥ x) k with ha
  set s := ∑ j, (τ b k j).im * x j with hs
  have hYk : ‖x‖ ≤ K * |a| := by
    refine (hKx x).trans (mul_le_mul_of_nonneg_left ?_ hK.le)
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]; exact hk i
  have hdiffb := (hV b hb).2 k
  have hclose : |s - a| ≤ g * ε * ‖x‖ := by
    have : s - a = ∑ j, ((τ b k j).im - (τ b₀ k j).im) * x j := by
      simp [hs, ha, Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, sub_mul]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |((τ b k j).im - (τ b₀ k j).im) * x j| ≤ ∑ _j : Fin g, ε * ‖x‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hdiffb j).le
            (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j) (abs_nonneg _) hεpos.le
      _ = g * ε * ‖x‖ := by simp [Finset.sum_const]; ring
  have hgε : (g : ℝ) * ε * K ≤ 1 / 2 := by
    have : (g : ℝ) * ε * K = g / (2 * (g + 1)) := by rw [hε]; field_simp
    rw [this, div_le_iff₀ (by positivity)]; linarith
  have h1 : |a| - |s| ≤ g * ε * ‖x‖ := by
    have := abs_sub_abs_le_abs_sub a s
    rw [abs_sub_comm] at this; linarith
  have h2 : K * (g * ε * ‖x‖) ≤ ‖x‖ / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hgε (norm_nonneg x)]
  have h3 : K * (|a| - |s|) ≤ K * (g * ε * ‖x‖) := mul_le_mul_of_nonneg_left h1 hK.le
  rw [mul_sub] at h3
  have hcs : c ≤ |s| := by
    rw [hc, div_le_iff₀ (by positivity)]; nlinarith
  refine le_norm_sub_one ?_ hcs
  rw [per_single_inl, norm_ch_row]

end GlobalTheory.RowChoice
