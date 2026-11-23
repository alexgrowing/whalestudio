import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PivotNeg

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

lemma spread_bound {n : ℕ} (f Δ : Fin n → ℝ) (h0 : ∑ k, Δ k = 0) :
    |∑ k, f k * Δ k| ≤ ((⨆ k, f k) - ⨅ k, f k) * ∑ k, |Δ k| := by
  have hb : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  have hb' : BddBelow (Set.range f) := (Set.finite_range f).bddBelow
  have hc : ∑ k, (⨅ j, f j) * Δ k = 0 := by rw [← Finset.mul_sum, h0, mul_zero]
  have key : ∑ k, f k * Δ k = ∑ k, (f k - ⨅ j, f j) * Δ k := by
    simp only [sub_mul, Finset.sum_sub_distrib, hc, sub_zero]
  rw [key, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have h1 : f k ≤ ⨆ j, f j := le_ciSup hb k
  have h2 : ⨅ j, f j ≤ f k := ciInf_le hb' k
  have h3 : |f k - ⨅ j, f j| ≤ (⨆ j, f j) - ⨅ j, f j := by
    rw [abs_of_nonneg (sub_nonneg.mpr h2)]
    linarith
  exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma norm_dOf {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    ‖dOf X y τ k‖ = |(dOf X y τ k).re| := by
  have h : dOf X y τ k = ((dOf X y τ k).re : ℂ) := by
    apply Complex.ext <;> simp [dOf_real X hy τ k]
  rw [h, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]

lemma ratio_eq {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    dmin X.Gm y τ k.succ / dmin X.Gm y τ k.castSucc = dOf X y τ k := by
  have hd0 : dmin X.Gm y τ k.castSucc ≠ 0 := by
    intro h0; have h := (hy τ).2 k.castSucc; rw [h0] at h; simp at h
  rw [dmin_succ X hy τ k]
  field_simp

lemma nfac_log {y : Frame X.Ψ r} (hy : y ∈ X.dom) (la : Wt X.Ψ r) :
    Real.log (X.nfac la y) = ∑ τ, ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X y τ k‖ := by
  unfold Data.nfac
  have hpos : ∀ τ k, 0 < ‖dOf X y τ k‖ := fun τ k => by
    rw [norm_dOf X hy τ k]
    apply abs_pos.2
    have h := sgn_dOf_pos X hy τ k
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (by
      rw [ratio_eq X hy τ k]; exact hpos τ k) _).ne')]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun k _ => (Real.rpow_pos_of_pos (by rw [ratio_eq X hy τ k]; exact hpos τ k) _).ne')]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ratio_eq X hy τ k, Real.log_rpow (hpos τ k)]

lemma sum_log_dOf {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) : ∑ k : Fin r, Real.log ‖dOf X (X.xZ x Z) τ k‖ = 0 := by
  have hy := xZ_mem_dom X hx ho hZ
  have hpos : ∀ k, ‖dOf X (X.xZ x Z) τ k‖ ≠ 0 := fun k => by
    rw [norm_dOf X hy τ k]
    apply (abs_pos.2 _).ne'
    have h := sgn_dOf_pos X hy τ k
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rw [← Real.log_prod (fun k _ => hpos k), ← norm_prod]
  have hp : ∏ k : Fin r, dOf X (X.xZ x Z) τ k = dmin X.Gm (X.xZ x Z) τ (Fin.last r) := by
    rw [dmin_prod X hy τ (Fin.last r)]
    rfl
  rw [hp]
  unfold dmin
  rw [gram_xZ X ho Z τ, lminor_last]
  unfold Gp
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_lowBlock, Matrix.det_diagonal, one_mul]
  rw [show ((X.lowBlock Z τ).map (starRingEnd ℂ)).det = (starRingEnd ℂ) (X.lowBlock Z τ).det from
    (RingHom.map_det _ _).symm, det_lowBlock, map_one, mul_one, norm_prod]
  rw [Finset.prod_eq_one fun k _ => ?_, Real.log_one]
  unfold sgn
  split_ifs <;> simp

lemma log_dOf_pos_bound {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : (k : ℕ) < X.p0) :
    Real.log ‖dOf X (X.xZ x Z) τ k‖ ≤ 0 ∧
      -Real.log ‖dOf X (X.xZ x Z) τ k‖ ≤ X.zN Z ^ 2 / (1 - X.zN Z ^ 2) := by
  have hy := xZ_mem_dom X hx ho hZ
  obtain ⟨h1, h2⟩ := pivot_pos X hx ho hZ τ k hk
  have h0 : 0 ≤ X.zN Z := le_trans (opN_nonneg _) (opN_le_zN X Z τ)
  have hu : X.zN Z ^ 2 < 1 := by nlinarith
  have htpos : 0 < (dOf X (X.xZ x Z) τ k).re := by linarith
  rw [norm_dOf X hy τ k, abs_of_pos htpos]
  refine ⟨Real.log_nonpos htpos.le h2, ?_⟩
  rw [← Real.log_inv]
  have h3 := Real.log_le_sub_one_of_pos (inv_pos.2 htpos)
  have h4 : (dOf X (X.xZ x Z) τ k).re⁻¹ ≤ (1 - X.zN Z ^ 2)⁻¹ := inv_anti₀ (by linarith) h1
  have hne : (1 - X.zN Z ^ 2) ≠ 0 := (by linarith : (0:ℝ) < 1 - X.zN Z ^ 2).ne'
  have h5 : (1 - X.zN Z ^ 2)⁻¹ - 1 = X.zN Z ^ 2 / (1 - X.zN Z ^ 2) := by
    field_simp
    ring
  linarith

lemma log_dOf_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : X.p0 ≤ (k : ℕ)) : 0 ≤ Real.log ‖dOf X (X.xZ x Z) τ k‖ := by
  have hy := xZ_mem_dom X hx ho hZ
  have hk' : k = nI X ⟨(k : ℕ) - X.p0, by have := k.isLt; omega⟩ := by
    apply Fin.ext; simp only [nI]; omega
  have h := pivot_neg X hx ho hZ τ ⟨(k : ℕ) - X.p0, by have := k.isLt; omega⟩
  rw [← hk'] at h
  rw [norm_dOf X hy τ k, abs_of_neg (by linarith)]
  exact Real.log_nonneg (by linarith)

lemma spread_nonneg (la : Wt X.Ψ r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  rcases isEmpty_or_nonempty (Fin r) with h | h
  · simp [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
  · exact sub_nonneg.mpr (ciInf_le_ciSup (Set.finite_range _).bddBelow (Set.finite_range _).bddAbove)

theorem nfac_xZ {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 10)
    {Z : X.Coord} (hZ : X.zN Z ≤ ρ) (la : Wt X.Ψ r) (w : ℝ) (hw : (∑ τ, X.spread la τ) ≤ w) :
    |Real.log (X.nfac la (X.xZ x Z)) - Real.log (X.nfac la x)| ≤ 4 * w * r * X.zN Z ^ 2 := by
  have hZ1 : X.zN Z < 1 := by linarith
  have hy := xZ_mem_dom X hx ho hZ1

  have hx1 : Real.log (X.nfac la x) = 0 := by
    have hn : ∀ τ (i : Fin (r + 1)), ‖dmin X.Gm x τ i‖ = 1 := by
      intro τ i
      unfold dmin
      rw [ho τ, lminor_diagonal, norm_prod]
      refine Finset.prod_eq_one fun j _ => ?_
      unfold sgn
      split_ifs <;> simp
    unfold Data.nfac
    rw [Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => by rw [norm_div, hn, hn, div_one,
      Real.one_rpow], Real.log_one]
  rw [hx1, sub_zero, nfac_log X hy la]
  set s := X.zN Z with hs
  have hs0 : 0 ≤ s := by
    rw [hs]
    unfold Data.zN
    exact Real.iSup_nonneg fun τ => opN_nonneg _
  have hu : s ^ 2 ≤ 1 / 100 := by nlinarith
  have hq : s ^ 2 / (1 - s ^ 2) ≤ 2 * s ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith

  have hτ : ∀ τ : X.Ψ, |∑ k : Fin r, (la τ k : ℝ) * Real.log ‖dOf X (X.xZ x Z) τ k‖| ≤
      X.spread la τ * (4 * r * s ^ 2) := by
    intro τ
    refine (spread_bound _ _ (sum_log_dOf X hx ho hZ1 τ)).trans ?_
    have hsp := spread_nonneg X la τ
    refine mul_le_mul_of_nonneg_left ?_ hsp

    have hsplit : ∑ k : Fin r, |Real.log ‖dOf X (X.xZ x Z) τ k‖| =
        ∑ k : Fin r, (if (k : ℕ) < X.p0 then -2 * Real.log ‖dOf X (X.xZ x Z) τ k‖ else 0) +
          ∑ k : Fin r, Real.log ‖dOf X (X.xZ x Z) τ k‖ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : (k : ℕ) < X.p0
      · rw [if_pos hk, abs_of_nonpos (log_dOf_pos_bound X hx ho hZ1 τ k hk).1]
        ring
      · rw [if_neg hk, abs_of_nonneg (log_dOf_neg X hx ho hZ1 τ k (not_lt.1 hk)), zero_add]
    rw [hsplit, sum_log_dOf X hx ho hZ1 τ, add_zero]
    calc ∑ k : Fin r, (if (k : ℕ) < X.p0 then -2 * Real.log ‖dOf X (X.xZ x Z) τ k‖ else 0)
        ≤ ∑ _k : Fin r, 2 * (2 * s ^ 2) := Finset.sum_le_sum fun k _ => by
          by_cases hk : (k : ℕ) < X.p0
          · rw [if_pos hk]
            have := (log_dOf_pos_bound X hx ho hZ1 τ k hk).2
            nlinarith
          · rw [if_neg hk]; positivity
      _ = 4 * r * s ^ 2 := by simp [Finset.card_univ]; ring
  have hsum : |∑ τ, ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X (X.xZ x Z) τ k‖| ≤
      ∑ τ, X.spread la τ * (4 * r * s ^ 2) / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    have e : ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X (X.xZ x Z) τ k‖ =
        -(1 / 2) * ∑ k : Fin r, (la τ k : ℝ) * Real.log ‖dOf X (X.xZ x Z) τ k‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [hτ τ]
  refine hsum.trans ?_
  rw [← Finset.sum_div, ← Finset.sum_mul]
  have hw0 : (0 : ℝ) ≤ 4 * r * s ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hw hw0
  have hw1 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => spread_nonneg X la τ) hw
  have hw2 : 0 ≤ w * (4 * r * s ^ 2) := mul_nonneg hw1 hw0
  nlinarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
