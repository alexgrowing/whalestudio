import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem window_scale_bounds (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (C : FC) (cD ch : ℝ) :
    ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L →
      2 ≤ L.sc.x ∧ Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n ∧ L.etaSz + 1 ≤ L.sc.w'' D.R.n ∧
      L.sc.w'' D.R.n ≤ L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ L.sc.b := by
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (max ch 0 + 10) (1 / 2) he (by norm_num)
  obtain ⟨CN, x3, h3⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 1 2 (2 * (max 1 C.GK.La * CN ^ 2)) 2 (by norm_num)
  refine ⟨max (max x1 x2) (max (max x3 x4) 2), fun D L hs hx hV => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx2 : x2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx3 : x3 ≤ L.sc.x :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx4 : x4 ≤ L.sc.x :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx5 : 2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  obtain ⟨hf, hm, -⟩ := h1 L.sc D.R hs hx1 hV.ranks
  obtain ⟨-, -, -, hb', -, hw, -⟩ := h2 L.sc hs hx2
  obtain ⟨-, -, hLa⟩ := h3 L.sc hs hx3
  have hLa' := (hLa { C.GK with La := max 1 C.GK.La } (le_max_left _ _)).2
  have h4' := h4 L.sc.x hx4
  clear h1 h2 h3 h4 hLa hx1 hx2 hx3 hx4 hx
  have hetaE := hV.eta_eq
  have hLaE := hV.La_eq
  have hbT := hV.bT_le
  have hx0 : 0 < L.sc.x := by linarith
  have hone : 1 ≤ L.sc.x := by linarith
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn0 : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
  obtain ⟨hw1, hw2, -⟩ := hw D.R.n hn1 (by linarith)
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hsq : L.sc.b ^ (1 - 1 / 2 : ℝ) = Real.sqrt L.sc.b := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hsq1 : 1 ≤ Real.sqrt L.sc.b := Real.one_le_sqrt.2 hb1
  rw [hsq] at hw1
  have hy1 : 1 ≤ L.sc.x ^ (max ch 0) := Real.one_le_rpow hone (le_max_right _ _)
  have hych : L.sc.x ^ ch ≤ L.sc.x ^ (max ch 0) := Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)
  have hsplit : L.sc.x ^ (max ch 0 + 10) = L.sc.x ^ (max ch 0) * L.sc.x ^ 10 := by
    rw [Real.rpow_add hx0]; norm_num
  rw [hsplit] at hw1 hb'
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := Real.exp_pos (L.sc.x ^ (L.sc.eps / 3))
    positivity
  have hf3 : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by
    have : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by norm_num
    rw [← this]; exact hf
  have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
    have := Real.rpow_le_rpow_of_exponent_le hone (show L.sc.eps ≤ 1 by rw [hs]; linarith)
    rwa [Real.rpow_one] at this
  have hxe0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
  have hd1 : L.sc.delta1 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hone (by have := L.sc.eps_pos; linarith)
  have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0.le _
  have hLa2 : L.LaG ≤ L.sc.x ^ 2 := by
    have ha : 0 ≤ Real.log L.sc.a := by
      apply Real.log_nonneg
      unfold Scale.a
      exact one_le_mul_of_one_le_of_one_le hone hb1
    have e1 : L.LaG ≤ G.La { C.GK with La := max 1 C.GK.La } L.sc := by
      rw [hLaE]
      unfold G.La
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) ha
    have e2 : L.sc.x ^ (2 : ℝ) = L.sc.x ^ 2 := by norm_num
    rw [Real.rpow_one, e2] at h4'
    have e3 : 0 ≤ max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 := by
      have : 0 ≤ max 1 C.GK.La := le_trans zero_le_one (le_max_left _ _)
      positivity
    have e4 : max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x) :=
      mul_le_mul_of_nonneg_left (by linarith) e3
    have e5 : G.La { C.GK with La := max 1 C.GK.La } L.sc ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) := hLa'
    linarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hh0 : (h0v L.sc ch : ℝ) ≤ 4 * L.sc.x ^ (max ch 0) := by
    unfold h0v
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le ch)
    push_cast
    linarith
  have hh00 : (0 : ℝ) ≤ h0v L.sc ch := Nat.cast_nonneg _
  have heta : L.etaSz ≤ L.sc.x * (4 * L.sc.x ^ (max ch 0)) := by
    rw [hetaE]; exact mul_le_mul hm hh0 hh00 hx0.le
  have hterm : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
      L.sc.x ^ 6 * L.sc.b' := by
    have e1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps ≤ L.sc.x ^ 3 * 1 * L.sc.x := by
      have e0 : 2 * (D.R.n : ℝ) ≤ L.sc.x ^ 3 := hfn ▸ hf3
      exact mul_le_mul (mul_le_mul e0 hd1 hd0 (by positivity)) hxe hxe0 (by positivity)
    have e2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG ≤ L.sc.x ^ 6 := by
      calc _ ≤ 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x ^ 2 :=
            mul_le_mul_of_nonneg_left hLa2 (by positivity)
        _ ≤ L.sc.x ^ 3 * 1 * L.sc.x * L.sc.x ^ 2 := mul_le_mul_of_nonneg_right e1 (by positivity)
        _ = _ := by ring
    rw [div_le_iff₀ (by linarith)]
    calc _ ≤ L.sc.x ^ 6 * L.sc.b' := mul_le_mul_of_nonneg_right e2 hb'0.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hk1
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hone
  clear hych hsplit hh0 hLa' h4' hw
  generalize L.sc.x ^ (max ch 0) = y at hw1 hb' hy1 heta
  have hp4 : (16 : ℝ) ≤ L.sc.x ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hx5 4
    linarith
  have hp6 : L.sc.x ≤ L.sc.x ^ 6 := le_self_pow₀ hone (by norm_num)
  have hp10 : 16 * L.sc.x ^ 6 ≤ L.sc.x ^ 10 := by
    calc _ ≤ L.sc.x ^ 4 * L.sc.x ^ 6 := mul_le_mul_of_nonneg_right hp4 (by positivity)
      _ = _ := by ring
  have hyx : L.sc.x ^ 10 ≤ y * L.sc.x ^ 10 := le_mul_of_one_le_left (by positivity) hy1
  have hyx1 : 1 ≤ y * L.sc.x ^ 10 := by linarith
  have hA : y * (16 * L.sc.x) ≤ y * L.sc.x ^ 10 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hB : 1 ≤ y * L.sc.x := one_le_mul_of_one_le_of_one_le hy1 hone
  have hC : y * L.sc.x ^ 10 ≤ Real.sqrt L.sc.b * (y * L.sc.x ^ 10) := le_mul_of_one_le_left (by linarith) hsq1
  have hD : L.sc.b' * (L.sc.x ^ 6 + 2) ≤ L.sc.b' * (y * L.sc.x ^ 10) :=
    mul_le_mul_of_nonneg_left (by linarith) hb'0.le
  refine ⟨hx5, le_trans (le_mul_of_one_le_right (by linarith) hyx1) hw1, by linarith, hw2,
    le_trans (le_mul_of_one_le_right hb'0.le hyx1) hb', fun t => ?_⟩
  have := hbT t
  linarith

theorem place_top_or_thick_or_thin (D : D7) (τ : D.what₂.Tau) :
    (∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t) ∨
      (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces ∨ D.host.IsThin (D.eTau τ : D.R.GG) := by
  by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    unfold Host.topPlaces at h1
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
    exact ⟨⟨t, ht⟩, e.symm⟩
  · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨(D.eTau τ).2, h1, h2⟩)

theorem szRow_sizeW_sizeBm_sizeXpp : SzRow (fun _ _ L => SizeW L ∧ SizeBm L ∧ SizeXpp L) := by
  intro eps he he' C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x0, h⟩ := window_scale_bounds eps he he' C cD ch
  refine ⟨x0, fun D L hs hx hV => ?_⟩
  obtain ⟨hx2, hW, heta, hwb, hbb, htop⟩ := h D L hs hx hV
  have heta0 := L.etaSz_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hdiv : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) hx0.le
  refine ⟨hW, ?_, ?_⟩
  · intro τ hm
    obtain ⟨-, -, ⟨b1, hb, h1, h2, h3⟩, -⟩ := hV.hc
    have hlow : L.sc.w'' D.R.n ≤ (b1 τ : ℝ) := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · rw [h1 τ t ht]
        have e1 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.2 hdiv
        have e2 := L.bT_ge t
        push_cast
        linarith
      · have e1 := Int.le_ceil L.sc.b
        have e2 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (h2 τ ht).1
        linarith
      · rw [h3 τ ht]; exact Int.le_ceil _
    rw [(hb τ _).1, (hb τ _).1]
    have e1 : ((D.R.m - 1 : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast Nat.sub_le _ _
    have e2 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz := by
      rw [hV.eta_eq]; exact mul_le_mul_of_nonneg_right e1 (Nat.cast_nonneg _)
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Nat.cast_zero, zero_mul, add_zero]
    linarith
  · intro j τ j' τ' hj1 hj2 hj1' hj2'
    have hup : wj D j τ ≤ 2 * L.sc.b := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j hj1 hj2 τ t ht).2
        have := htop t
        linarith
      · have := (L.win_thick j hj1 hj2 τ ht).2
        linarith
      · have := (L.win_thin j hj1 hj2 τ ht).2
        linarith
    have hlo : L.sc.w'' D.R.n ≤ wj D j' τ' := by
      rcases place_top_or_thick_or_thin D τ' with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j' hj1' hj2' τ' t ht).1
        have := L.bT_ge t
        linarith
      · have := (L.win_thick j' hj1' hj2' τ' ht).1
        linarith
      · exact (L.win_thin j' hj1' hj2' τ' ht).1
    have hw0 : 0 < L.sc.w'' D.R.n := by linarith
    have hb0 : 0 < L.sc.b := by linarith
    have hX0 : 0 ≤ L.sc.X'' D.R.n := by
      unfold Scale.X'' Scale.a; positivity
    have hXw : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b := by
      unfold Scale.X'' Scale.a; exact div_mul_cancel₀ _ hw0.ne'
    calc wj D j τ ≤ 2 * L.sc.b := hup
      _ ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx2 hb0.le
      _ = _ := hXw.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hX0

end GlobalTheory.EX
