import ReciprocityTheory.AnalyticForms.LeviForms.RegChartB

namespace ReciprocityTheory.AnForm.P.RegularChartScaling

open MeasureTheory Metric Filter Topology Set
open ReciprocityTheory.AnForm.A

noncomputable section

variable {D : ℕ}

lemma closedBall_sub_of {z : Fin D → ℂ} {r s R : ℝ} (hz : z ∈ ball (0 : Fin D → ℂ) r)
    (hs : s ≤ R - r) : closedBall z s ⊆ ball 0 R := by
  intro x hx
  rw [mem_closedBall_iff_norm] at hx
  rw [mem_ball_zero_iff] at hz ⊢
  have := norm_sub_norm_le x z
  linarith

lemma fifth_volume_constant_nonneg {S : Finset (Fin D)} (m : Fin D → ℕ) {u : (Fin D → ℂ) → ℝ} {R C₅ : ℝ}
    (hR2 : R ≤ 2) (hR : 1 < R)
    (hb : ∀ z ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) :
    0 ≤ C₅ := by
  obtain ⟨x, hx, hf, hn⟩ := exists_far_point (0 : Fin D → ℂ) (s := 1 / 2) (by norm_num)
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := by rw [mem_ball_zero_iff]; simp at hn; linarith
  have hxA := not_mem_coordDiv_of (S := S) (by norm_num : (0 : ℝ) < 1 / 2) hf
  obtain ⟨h1, h2⟩ := hb x ⟨hxB, hxA⟩
  have h3 : 1 ≤ Real.log (rLoc S m x) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (rLoc_ge S m (norm_coord_le_of_ball hR2 hxB))
  nlinarith

theorem oscGen {S : Finset (Fin D)} (m : Fin D → ℕ) {u : (Fin D → ℂ) → ℝ} {R C₅ : ℝ}
    (hR2 : R ≤ 2) (hR : 5 / 4 < R)
    (hc : ContinuousOn u (ball 0 R \ coordDiv S)) (hp : IsPsh (ball 0 R \ coordDiv S) u)
    (hb : ∀ z ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅)
    {C₁ : ℝ} (hC₁ : 1 ≤ C₁) :
    ∃ C ℓ₀ : ℝ, 1 ≤ C ∧ ∀ t, 0 < t → ℓ₀ ≤ Real.log (1 / t) →
      Real.exp 1 ≤ Real.log (1 / t) ∧ C₁ * t ≤ (R - 5 / 4) / 2 ∧
      ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
        -C * Real.log (Real.log (1 / t)) ≤ pmoff S u z (t / (8 * C₁)) ∧
        pmoff S u z (C₁ * t) - pmoff S u z (t / (4 * C₁)) ≤ epsT C t := by
  have hC₅ : 0 ≤ C₅ := fifth_volume_constant_nonneg m hR2 (by linarith) hb
  have hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅ := fun x hx => (hb x hx).2
  set R' := R - 5 / 4 with hR'
  have hR'0 : 0 < R' := by linarith
  have hC0 : 0 < C₁ := by linarith
  have hlC : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁
  have hl8 : 0 < Real.log (8 * C₁) := Real.log_pos (by linarith)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set Λ := Real.log C₁ + Real.log (8 * C₁) with hΛ
  have hΛ0 : 0 < Λ := by linarith
  set K₁ := Real.exp 1 + mTot S m * (Real.log 4 + 2 * Real.log (8 * C₁) + 2) with hK₁
  have hmT := mTot_nonneg S m
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨6 * C₅ * Λ + 2 * C₅ + 1,
    max (max (Real.exp 1) K₁) (max (Real.log (2 * C₁ / R')) (2 * (Real.log C₁ - Real.log R'))),
    by have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hC₅) hΛ0.le; linarith,
    fun t ht hℓ => ?_⟩
  set ℓ := Real.log (1 / t) with hℓdef
  have hℓt : Real.log t = -ℓ := by rw [hℓdef, one_div, Real.log_inv, neg_neg]
  have h1 : Real.exp 1 ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hℓ
  have h2 : K₁ ≤ ℓ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hℓ
  have h3 : Real.log (2 * C₁ / R') ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hℓ
  have h4 : 2 * (Real.log C₁ - Real.log R') ≤ ℓ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hℓ
  have hℓ1 : 1 ≤ ℓ := he1.trans h1
  have hlℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) h1
  have hteq : t = Real.exp (-ℓ) := by rw [← hℓt, Real.exp_log ht]
  have hCt : C₁ * t ≤ R' / 2 := by
    have : 2 * C₁ / R' ≤ Real.exp ℓ := by
      rw [← Real.exp_log (by positivity : 0 < 2 * C₁ / R')]; exact Real.exp_le_exp.2 h3
    rw [hteq, Real.exp_neg]
    rw [div_le_iff₀ hR'0] at this
    have hE := Real.exp_pos ℓ
    rw [mul_inv_le_iff₀ hE]
    nlinarith
  refine ⟨h1, hCt, fun z hz => ?_⟩

  set κ := 2 * C₅ * Real.log ℓ + 1 with hκ
  obtain ⟨w, -, hW1, hW2, hW3⟩ := ext_exists S (by linarith : (0 : ℝ) < R) hC₅ hc hp hub κ
  have hwu : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ w x := fun x hx => by
    rw [hW2 x hx]; exact le_max_left _ _
  set s₈ := t / (8 * C₁) with hs₈
  set s₄ := t / (4 * C₁) with hs₄
  have hs₈0 : 0 < s₈ := by positivity
  have hs₄0 : 0 < s₄ := by positivity
  have hs84 : s₈ < s₄ := by
    rw [hs₈, hs₄]; exact div_lt_div_of_pos_left ht (by positivity) (by linarith)
  have hs4C : s₄ ≤ C₁ * t := by
    rw [hs₄, div_le_iff₀ (by positivity)]
    have h4c : 1 ≤ 4 * C₁ * C₁ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4c ht.le]
  have hsub : ∀ s, s ≤ R' → closedBall z s ⊆ ball 0 R := fun s hs =>
    closedBall_sub_of hz (by linarith)
  have hCtR : C₁ * t ≤ R' := by linarith

  have hlow : -C₅ * (2 * Real.log ℓ) ≤ pmoff S u z s₈ := by
    refine le_trans ?_ (pmo_lower hR2 hC₅ m hb hs₈0 (hsub _ (by linarith)))
    have hlog : Real.log (4 / s₈ ^ 2) = Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁) := by
      rw [Real.log_div (by norm_num) (by positivity), Real.log_pow, hs₈,
        Real.log_div ht.ne' (by positivity), hℓt]
      push_cast; ring
    rw [hlog]
    have hK0 : 0 < K₁ := by
      have : 0 ≤ mTot S m * (Real.log 4 + 2 * Real.log (8 * C₁) + 2) :=
        mul_nonneg hmT (by linarith)
      linarith [Real.exp_pos 1]
    have hA : Real.exp 1 + mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)) ≤ K₁ * ℓ := by
      rw [hK₁]
      have e1 : Real.exp 1 ≤ Real.exp 1 * ℓ := le_mul_of_one_le_right (Real.exp_pos 1).le hℓ1
      have e2 : mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)) ≤
          mTot S m * (Real.log 4 + 2 * Real.log (8 * C₁) + 2) * ℓ := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hmT
        nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log 4 + 2 * Real.log (8 * C₁))
          (by linarith : (0:ℝ) ≤ ℓ - 1)]
      linarith
    have hApos : 0 < Real.exp 1 + mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)) := by
      have : 0 ≤ mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)) :=
        mul_nonneg hmT (by linarith)
      linarith [Real.exp_pos 1]
    have hB : Real.log (Real.exp 1 + mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)))
        ≤ 2 * Real.log ℓ := by
      calc _ ≤ Real.log (K₁ * ℓ) := Real.log_le_log hApos hA
        _ = Real.log K₁ + Real.log ℓ := Real.log_mul hK0.ne' (by linarith)
        _ ≤ 2 * Real.log ℓ := by linarith [Real.log_le_log hK0 h2]
    have := mul_le_mul_of_nonneg_left hB hC₅
    linarith
  have hκlow : -κ < pmoff S u z s₄ := by
    have := pmo_mono hub hs₈0 hs84.le (hsub s₄ (by linarith))
    rw [hκ]; linarith

  set g : ℝ → ℝ := fun σ => polyMax w z (Real.exp σ) with hg
  have hconv := (polyMaxLogConvex_thm D (ball 0 R) w z R' isOpen_ball hW1 hR'0 (hsub R' le_rfl)).1
  set a := Real.log s₈ with ha
  set b := Real.log (C₁ * t) with hbdef
  set σ := Real.log R' with hσ
  have ha' : a = -ℓ - Real.log (8 * C₁) := by
    rw [ha, hs₈, Real.log_div ht.ne' (by positivity), hℓt]
  have hb' : b = Real.log C₁ - ℓ := by
    rw [hbdef, Real.log_mul hC0.ne' ht.ne', hℓt]; ring
  have hab : a < b := by rw [ha', hb']; linarith
  have hbσ : ℓ / 2 ≤ σ - b := by rw [hb']; linarith
  have hbσ' : b < σ := by linarith
  have hslope := hconv.slope_mono_adjacent (by simp only [Set.mem_Iic]; linarith)
    (by simp only [Set.mem_Iic]; exact le_rfl) hab hbσ'
  have hga : g a = polyMax w z s₈ := by simp only [hg, ha, Real.exp_log hs₈0]
  have hgb : g b = polyMax w z (C₁ * t) := by simp only [hg, hbdef, Real.exp_log (mul_pos hC0 ht)]
  have hgσ : g σ ≤ C₅ := by
    simp only [hg, hσ, Real.exp_log hR'0]
    refine polyMax_le' hR'0.le fun x hx => le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨y, hy, -, hwy⟩ := hW3 x (hsub R' le_rfl hx) δ hδ
    have : max (u y) (-κ) ≤ C₅ := max_le (hub y hy) (by
      have := mul_nonneg hC₅ (by linarith : (0:ℝ) ≤ Real.log ℓ); rw [hκ]; linarith)
    linarith
  have hga_low : -C₅ * (2 * Real.log ℓ) ≤ g a := by
    rw [hga]; exact hlow.trans (pmo_le_polyMax hW1.1 hwu hs₈0 (hsub _ (by linarith)))
  have hga_up : g a ≤ pmoff S u z s₄ := by
    rw [hga]
    have := polyMax_le_pmo hub hW3 hs₈0.le hs84 (hsub s₄ (by linarith))
    rwa [max_eq_left hκlow.le] at this
  have hgb_up : pmoff S u z (C₁ * t) ≤ g b := by
    rw [hgb]; exact pmo_le_polyMax hW1.1 hwu (by positivity) (hsub _ hCtR)
  have hgab : g a ≤ g b := by
    have := polyMax_mono' hW1.1 hs₈0.le (by linarith) (hsub _ hCtR) (z := z)
    rw [hga, hgb]; exact this

  have hCl : 0 ≤ C₅ * Real.log ℓ := mul_nonneg hC₅ (by linarith)
  have hN : g σ - g b ≤ C₅ + 2 * C₅ * Real.log ℓ := by linarith
  have hN0 : 0 ≤ C₅ + 2 * C₅ * Real.log ℓ := by linarith
  have hba : b - a = Λ := by rw [ha', hb', hΛ]; ring
  have hosc : g b - g a ≤ Λ * ((C₅ + 2 * C₅ * Real.log ℓ) / (ℓ / 2)) := by
    rw [hba] at hslope
    rw [div_le_iff₀ hΛ0] at hslope
    have q1 : (g σ - g b) / (σ - b) ≤ (C₅ + 2 * C₅ * Real.log ℓ) / (σ - b) :=
      div_le_div_of_nonneg_right hN (by linarith)
    have q2 : (C₅ + 2 * C₅ * Real.log ℓ) / (σ - b) ≤ (C₅ + 2 * C₅ * Real.log ℓ) / (ℓ / 2) :=
      div_le_div_of_nonneg_left hN0 (by linarith) hbσ
    have := mul_le_mul_of_nonneg_right (q1.trans q2) hΛ0.le
    linarith
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hlow
    have : 2 * C₅ ≤ 6 * C₅ * Λ + 2 * C₅ + 1 := by
      have := mul_nonneg hC₅ hΛ0.le; linarith
    have := mul_le_mul_of_nonneg_right this (by linarith : (0:ℝ) ≤ Real.log ℓ)
    linarith
  · have hℓ0 : 0 < ℓ := by linarith
    have key : Λ * ((C₅ + 2 * C₅ * Real.log ℓ) / (ℓ / 2)) ≤ epsT (6 * C₅ * Λ + 2 * C₅ + 1) t := by
      have e : Λ * ((C₅ + 2 * C₅ * Real.log ℓ) / (ℓ / 2)) =
          2 * Λ * (C₅ + 2 * C₅ * Real.log ℓ) / ℓ := by
        field_simp
      rw [e, epsT, ← hℓdef]
      refine div_le_div_of_nonneg_right ?_ hℓ0.le
      have n1 : C₅ ≤ C₅ * Real.log ℓ := le_mul_of_one_le_right hC₅ hlℓ
      have n2 : 0 ≤ Λ * (C₅ * Real.log ℓ) := mul_nonneg hΛ0.le hCl
      have n3 : Λ * C₅ ≤ Λ * (C₅ * Real.log ℓ) := mul_le_mul_of_nonneg_left n1 hΛ0.le
      have n4 : 0 ≤ (2 * C₅ + 1) * Real.log ℓ := mul_nonneg (by linarith) (by linarith)
      linarith
    linarith

end

end ReciprocityTheory.AnForm.P.RegularChartScaling
