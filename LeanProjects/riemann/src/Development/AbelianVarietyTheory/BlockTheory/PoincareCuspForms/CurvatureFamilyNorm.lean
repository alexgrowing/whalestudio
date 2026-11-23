import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

namespace GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def de2 (X : Data E r) : Wt X.Ψ r := fun _ i => if (i : ℕ) < X.p0 then -1 else 1

def frameWt (X : Data E r) (a : Wt X.Ψ r) (h : ℤ) : Wt X.Ψ r := a + h • de2 X

def IsGap (X : Data E r) (i j : Fin r) : Prop := (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ X.p0

def rd (X : Data E r) : ℝ := |(discr E : ℝ)| ^ (1 / (2 * (X.Ψ.card : ℝ)))

def RR (X : Data E r) : ℝ := rd X ^ 7

def dp (X : Data E r) : ℝ := 2 * (X.Ψ.card : ℝ) * X.p0

def g0half (r : ℕ) : ℕ := 5 ^ 4 * r

def g0 (r : ℕ) : ℕ := 2 * g0half r

def a1 (X : Data E r) : ℝ := (X.Ψ.card : ℝ) / (5 ^ 4 * rd X ^ 2)

def bb (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2

def Crh (X : Data E r) : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ)

structure Shape (X : Data E r) : Prop where
  p0_pos : 0 < X.p0
  witt : 2 * X.p0 ≤ r
  r_ge : 8 ≤ r
  D_ge : 2 ≤ nd X

structure Weights (X : Data E r) where
  shape : Shape X
  T : ℕ
  i : ℕ
  c : ℝ
  hW : ℕ
  hF : ℕ
  aK : Wt X.Ψ r
  aW : Wt X.Ψ r
  i_pos : 0 < i
  c_pos : 0 < c
  T_cols : (nd X + 2) * (2 * hW) + 2 * r ≤ T
  T_forty : 40 * (nd X + 2) ≤ T
  T_sq : 11 * nd X ^ 2 ≤ T
  cols_lo : 8 * X.Ψ.card * r + 4 ≤ 2 * hF
  cols_hi : 2 * hF ≤ 2 * hW
  Tcg : (T : ℝ) * c * g0 r ≤ 1
  cRR : (g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X ^ 2 * c ≤ 1
  b_cut : bb X < 3.8 * T - 2 * T
  b_onto : bb X ^ 2 * Crh X + bb X < 1.9 * ((nd X : ℝ) + 2) * T
  gap_big : ∀ τ a b, IsGap X a b →
    ((T : ℤ) + nd X + 2) * ((T : ℤ) + nd X + 2 + 2 * r) ≤ aK τ a - aK τ b + 2
  plus_big : ∀ τ (a : Fin r), (a : ℕ) + 1 = r → 2 * (T : ℤ) ^ 2 ≤ aK τ a
  minus_big : ∀ τ (a : Fin r), (a : ℕ) = 0 → 2 * (T : ℤ) ^ 2 ≤ -aK τ a
  gap_div : ∀ τ a b, IsGap X a b →
    aK τ a - aK τ b + 2 - ((T : ℤ) + nd X + 2) * (aW τ a - aW τ b) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)
  plus_div : ∀ τ (a : Fin r), (a : ℕ) + 1 = r →
    aK τ a - ((T : ℤ) + nd X + 2) * aW τ a - ((nd X : ℤ) + 2) * (2 * hW) - 2 * r ∈
      Set.Ico (0 : ℤ) (T + nd X + 2)
  minus_div : ∀ τ (a : Fin r), (a : ℕ) = 0 →
    -aK τ a - ((T : ℤ) + nd X + 2) * (-aW τ a) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)

namespace Weights

variable {X : Data E r} (w : Weights X)

def L : Wt X.Ψ r := frameWt X w.aW w.hW

def Fp : Wt X.Ψ r := frameWt X (w.aK - (w.T : ℤ) • w.aW) w.hF

def ka : Wt X.Ψ r := w.Fp + (w.T : ℤ) • w.L

def twoG₁ : Wt X.Ψ r := (2 : ℤ) • w.L - de2 X

def G₂ : Wt X.Ψ r := ((nd X : ℤ) + 4) • w.L - w.Fp

def n₁ : ℕ := w.i * g0 r

def wEt : Wt X.Ψ r := frameWt X 0 (w.i * g0half r : ℕ)

def rem : Wt X.Ψ r := w.Fp - ((nd X : ℤ) + 2) • w.L - kapW X

def c1 : ℝ := RR X * w.T * w.c * dp X ^ 2 * X.p0 / 2

def t : ℝ := 1 + w.c1 / a1 X

theorem weight_eta_sq_theta : (2 : ℤ) • w.wEt + (w.n₁ : ℤ) • w.twoG₁ = (2 * (w.n₁ : ℤ)) • w.L := by
  funext τ a
  simp only [wEt, twoG₁, frameWt, n₁, g0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  push_cast
  ring

theorem weight_product : (2 * (w.n₁ : ℤ)) • (w.ka + w.G₂) + (2 * (w.n₁ : ℤ)) • w.twoG₁ + (4 : ℤ) • w.wEt =
    (2 * (w.n₁ : ℤ) * (w.T + nd X + 6)) • w.L := by
  funext τ a
  simp only [wEt, twoG₁, ka, G₂, n₁, g0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [frameWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  push_cast
  ring

theorem pairing_rem (τ : X.Ψ) (a b : Fin r) (ha : (a : ℕ) = 0) (hb : (b : ℕ) + 1 = r) :
    2 * (w.hF : ℤ) + 2 ≤ w.rem τ b - w.rem τ a := by
  have h1 := (w.plus_div τ b hb).1
  have h2 := (w.minus_div τ a ha).1
  have hp := w.shape.p0_pos
  have hq := w.shape.witt
  have e1 : de2 X τ a = -1 := by simp only [de2]; rw [if_pos (by omega)]
  have e2 : de2 X τ b = 1 := by simp only [de2]; rw [if_neg (by omega)]
  have e3 : ((b : ℕ) : ℤ) = r - 1 := by omega
  simp only [rem, Fp, L, frameWt, kapW, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e1, e2, e3, ha]
  push_cast
  nlinarith

theorem pairing_L (τ : X.Ψ) (a b : Fin r) (ha : (a : ℕ) = 0) (hb : (b : ℕ) + 1 = r) :
    38 * (w.T : ℤ) ≤ 10 * (w.L τ b - w.L τ a) := by
  have h1 := (w.plus_div τ b hb).2
  have h2 := (w.minus_div τ a ha).2
  have h3 := w.plus_big τ b hb
  have h4 := w.minus_big τ a ha
  have hp := w.shape.p0_pos
  have hq := w.shape.witt
  have h5 : ((nd X : ℤ) + 2) * (2 * w.hW) + 2 * r ≤ w.T := by exact_mod_cast w.T_cols
  have h6 : 40 * ((nd X : ℤ) + 2) ≤ w.T := by exact_mod_cast w.T_forty
  have hD : (0 : ℤ) ≤ nd X := by positivity
  have hh : (0 : ℤ) ≤ w.hW := by positivity
  have e1 : de2 X τ a = -1 := by simp only [de2]; rw [if_pos (by omega)]
  have e2 : de2 X τ b = 1 := by simp only [de2]; rw [if_neg (by omega)]
  have key : ∀ u : ℤ, 2 * (w.T : ℤ) ^ 2 - w.T < ((w.T : ℤ) + nd X + 2) * (u + 1) → 19 * (w.T : ℤ) ≤ 10 * u := by
    intro u hu
    by_contra hc
    have hc' : 10 * (u + 1) ≤ 19 * (w.T : ℤ) + 9 := by omega
    have : ((w.T : ℤ) + nd X + 2) * (10 * (u + 1)) ≤ ((w.T : ℤ) + nd X + 2) * (19 * w.T + 9) :=
      mul_le_mul_of_nonneg_left hc' (by positivity)
    nlinarith
  have k1 := key (w.aW τ b) (by nlinarith)
  have k2 := key (-w.aW τ a) (by nlinarith)
  simp only [L, frameWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1, e2]
  linarith

theorem t_mul_r_le : w.t * r ≤ 2 * w.T := by
  have hrd : 1 ≤ rd X := by
    apply Real.one_le_rpow _ (by positivity)
    have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
    exact_mod_cast this
  have hr : (r : ℝ) ≤ w.T := by exact_mod_cast (by have := w.T_cols; omega : r ≤ w.T)
  have hT : (0 : ℝ) ≤ w.T := by positivity
  have hc := w.c_pos
  have hRR : rd X ^ 2 ≤ RR X := pow_le_pow_right₀ hrd (by norm_num)
  have hR0 : 0 ≤ RR X := by unfold RR; positivity
  have key : w.c1 / a1 X * r ≤ w.T := by
    rcases Nat.eq_zero_or_pos X.Ψ.card with h0 | h0
    · simp [a1, h0]
    · have hf : (0 : ℝ) < X.Ψ.card := by exact_mod_cast h0
      have e : w.c1 / a1 X * r =
          ((g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X * w.c) * rd X ^ 2 * w.T := by
        simp only [c1, a1, dp, g0, g0half]
        push_cast
        field_simp
        ring
      have h2 : ((g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X * w.c) * rd X ^ 2 ≤ 1 := by
        refine le_trans (mul_le_mul_of_nonneg_left hRR (by positivity)) (le_trans (le_of_eq ?_) w.cRR)
        ring
      rw [e]
      nlinarith
  simp only [t]
  linarith

end Weights

theorem nonempty_weights (X : Data E r) (h : Shape X) : Nonempty (Weights X) := by
  obtain ⟨T, hT1, hT2, hT3, hT4, hT5⟩ : ∃ T : ℕ,
      (nd X + 2) * (2 * (4 * X.Ψ.card * r + 2)) + 2 * r ≤ T ∧ 40 * (nd X + 2) ≤ T ∧
      11 * nd X ^ 2 ≤ T ∧ bb X < T ∧ bb X ^ 2 * Crh X + bb X < T := by
    obtain ⟨n, hn⟩ := exists_nat_gt (bb X)
    obtain ⟨m, hm⟩ := exists_nat_gt (bb X ^ 2 * Crh X + bb X)
    refine ⟨(nd X + 2) * (2 * (4 * X.Ψ.card * r + 2)) + 2 * r + 40 * (nd X + 2) + 11 * nd X ^ 2 + n + m,
      by omega, by omega, by omega, hn.trans_le (by exact_mod_cast (by omega)),
      hm.trans_le (by exact_mod_cast (by omega))⟩
  have hp := h.p0_pos
  have hq := h.witt
  have hr := h.r_ge
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hg : (0 : ℝ) < g0 r := by
    have : 0 < g0 r := by simp only [g0, g0half]; omega
    exact_mod_cast this
  set A : ℝ := (T : ℝ) * g0 r with hA
  set B : ℝ := (g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X ^ 2 with hB
  have hA0 : 0 < A := by positivity
  have hB0 : 0 ≤ B := by positivity
  let Tp : ℤ := T + nd X + 2
  let g : ℤ := Tp + 2 * r
  let aW : Wt X.Ψ r := fun _ a =>
    if (a : ℕ) < X.p0 then -(2 * (T : ℤ)) - g * (a : ℕ) else 2 * T + g * ((r : ℤ) - 1 - (a : ℕ))
  let s : Wt X.Ψ r := fun _ a =>
    if (a : ℕ) < X.p0 then 2 * ((a : ℕ) : ℤ) else
      ((nd X : ℤ) + 2) * (2 * ((4 * X.Ψ.card * r + 2 : ℕ) : ℤ)) + 2 * r - 2 * ((r : ℤ) - 1 - (a : ℕ))
  have hTp : (0 : ℤ) < T + nd X + 2 := by positivity
  have hgap : ∀ τ a b, IsGap X a b → aW τ a - aW τ b = g ∧ s τ a - s τ b = -2 := by
    rintro τ a b ⟨h1, h2⟩
    have e : ((b : ℕ) : ℤ) = (a : ℕ) + 1 := by omega
    by_cases ha : (a : ℕ) < X.p0
    · have hb : (b : ℕ) < X.p0 := by omega
      simp only [aW, s, if_pos ha, if_pos hb, e]
      constructor <;> ring
    · have hb : ¬ (b : ℕ) < X.p0 := by omega
      simp only [aW, s, if_neg ha, if_neg hb, e]
      constructor <;> ring
  have hplus : ∀ τ (a : Fin r), (a : ℕ) + 1 = r → aW τ a = 2 * T ∧
      s τ a = ((nd X : ℤ) + 2) * (2 * ((4 * X.Ψ.card * r + 2 : ℕ) : ℤ)) + 2 * r := by
    intro τ a ha
    have e : ((a : ℕ) : ℤ) = r - 1 := by omega
    have hb : ¬ (a : ℕ) < X.p0 := by omega
    simp only [aW, s, if_neg hb, e]
    constructor <;> ring
  have hminus : ∀ τ (a : Fin r), (a : ℕ) = 0 → aW τ a = -(2 * T) ∧ s τ a = 0 := by
    intro τ a ha
    have hb : (a : ℕ) < X.p0 := by omega
    simp only [aW, s, if_pos hb]
    rw [ha]
    constructor <;> simp
  have hD : (0 : ℝ) ≤ nd X := by positivity
  refine ⟨{
    shape := h, T := T, i := 1, c := 1 / (A + B), hW := 4 * X.Ψ.card * r + 2, hF := 4 * X.Ψ.card * r + 2
    aK := fun τ a => Tp * aW τ a + s τ a, aW := aW
    i_pos := one_pos, c_pos := by positivity, T_cols := hT1, T_forty := hT2, T_sq := hT3
    cols_lo := by apply le_of_eq; ring
    cols_hi := le_rfl
    Tcg := ?_, cRR := ?_, b_cut := by linarith, b_onto := by nlinarith
    gap_big := ?_, plus_big := ?_, minus_big := ?_, gap_div := ?_, plus_div := ?_, minus_div := ?_ }⟩
  · have : (T : ℝ) * (1 / (A + B)) * g0 r = A / (A + B) := by rw [hA]; ring
    rw [this, div_le_one (by positivity)]; linarith
  · rw [← hB, mul_one_div, div_le_one (by positivity)]; linarith
  · intro τ a b hab
    obtain ⟨h1, h2⟩ := hgap τ a b hab
    apply le_of_eq
    simp only [Tp, g] at h1 ⊢
    linear_combination (-((T : ℤ) + nd X + 2)) * h1 - h2
  · intro τ a ha
    obtain ⟨h1, h2⟩ := hplus τ a ha
    simp only [h1, h2, Tp]
    have : (0 : ℤ) ≤ ((nd X : ℤ) + 2) * (2 * ((4 * X.Ψ.card * r + 2 : ℕ) : ℤ)) + 2 * r := by positivity
    have : (0 : ℤ) ≤ (T : ℤ) * (nd X + 2) := by positivity
    nlinarith
  · intro τ a ha
    obtain ⟨h1, h2⟩ := hminus τ a ha
    simp only [h1, h2, Tp]
    have : (0 : ℤ) ≤ (T : ℤ) * (nd X + 2) := by positivity
    nlinarith
  · intro τ a b hab
    obtain ⟨h1, h2⟩ := hgap τ a b hab
    have : Tp * aW τ a + s τ a - (Tp * aW τ b + s τ b) + 2 -
        ((T : ℤ) + nd X + 2) * (aW τ a - aW τ b) = 0 := by
      simp only [Tp]; linear_combination h2
    rw [this]; exact ⟨le_rfl, hTp⟩
  · intro τ a ha
    obtain ⟨h1, h2⟩ := hplus τ a ha
    have : Tp * aW τ a + s τ a - ((T : ℤ) + nd X + 2) * aW τ a -
        ((nd X : ℤ) + 2) * (2 * ((4 * X.Ψ.card * r + 2 : ℕ) : ℤ)) - 2 * r = 0 := by
      simp only [Tp]; linear_combination h2
    rw [this]; exact ⟨le_rfl, hTp⟩
  · intro τ a ha
    obtain ⟨h1, h2⟩ := hminus τ a ha
    have : -(Tp * aW τ a + s τ a) - ((T : ℤ) + nd X + 2) * (-aW τ a) = 0 := by
      simp only [Tp]; linear_combination -h2
    rw [this]; exact ⟨le_rfl, hTp⟩

def lev (X : Data E r) (x0 : Frame X.Ψ r) (u : Frame X.Ψ r → ℝ) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((u (cpt X x0 y) : ℝ) : ℂ)) z ξ).re

def curv (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  lev X x0 (phla X la) z ξ

def curvDe (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  curv X x0 (de2 X) z ξ / 2

def omRh (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z ξ).re

def IsInv (X : Data E r) (u : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x) ∧ ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, u (lact γ x) = u x

def famNorm (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm la (w j) x ^ 2)

structure ThetaInputs (X : Data E r) extends Weights X where

  N : ℕ
  w : Fin N → Frame X.Ψ r → ℂ
  et : Frame X.Ψ r → ℂ
  th₁ : Frame X.Ψ r → ℂ
  th₂ : Frame X.Ψ r → ℂ
  thp : Frame X.Ψ r → ℂ
  phi : Frame X.Ψ r → ℝ
  mu : ℝ
  ps0 : Frame X.Ψ r → ℝ
  w_cusp : ∀ j, w j ∈ X.SS toWeights.L
  et_bdd : X.IsBddSec toWeights.wEt et
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  th₁_cusp : th₁ ∈ X.SS toWeights.twoG₁
  th₁_ne : ∃ x ∈ X.dom, th₁ x ≠ 0
  th₂_cusp : th₂ ∈ X.SS toWeights.G₂
  th₂_ne : ∃ x ∈ X.dom, th₂ x ≠ 0
  thp_cusp : thp ∈ X.SS toWeights.Fp
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0
  phi_inv : IsInv X phi
  phi_nonneg : ∀ x ∈ X.dom, 0 ≤ phi x
  phi_lower : ∀ x ∈ X.dom, X.la1 x < Real.sqrt X.Ψ.card * Real.exp (-mu) →
    1 ≤ 4 * RR X * dp X ^ 2 * X.la1 x ^ 2 * phi x
  phi_upper : ∀ x ∈ X.dom, 2 * X.la1 x ^ 2 * phi x ≤ X.p0 * dp X ^ 2
  w_lower : ∃ C : ℝ, ∀ x ∈ X.dom, Real.exp (-(C + c * phi x)) ≤ famNorm X toWeights.L w x
  et_upper : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm toWeights.wEt et x ≤ Real.exp (-(i * (phi x - C)))
  potential_smooth : ContDiffOn ℝ ∞ ps0 X.dom
  potential_invariant : IsInv X ps0
  potential_bounded : ∃ C : ℝ, ∀ x ∈ X.dom, ps0 x ≤ C
  curvature_lower_bound : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, -(r * curvDe X x0 z ξ) ≤ lev X x0 ps0 z ξ
  potential_decay : ∃ A : ℝ, ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ, X.IsIso ξ →
    (∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
    ps0 x ≤ C + A * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a1 X * ⨅ τ, X.tt ξ x τ
  curv_L : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, ξ ≠ 0 → 0 < curv X x0 toWeights.L z ξ
  curv_G₁ : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, ξ ≠ 0 →
    curvDe X x0 z ξ < curv X x0 toWeights.L z ξ
  margin_cut : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    curv X x0 toWeights.L z ξ + 3.8 * T * omRh X x0 z ξ ≤
      curv X x0 ((2 : ℤ) • toWeights.L + toWeights.rem) z ξ
  margin_twist : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    curv X x0 toWeights.L z ξ + (3.8 * T - 2 * T) * omRh X x0 z ξ ≤
      curv X x0 ((2 : ℤ) • toWeights.L + toWeights.rem) z ξ - toWeights.t * r * curvDe X x0 z ξ
  margin_onto : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    1.9 * ((nd X : ℝ) + 2) * T * omRh X x0 z ξ ≤ curv X x0 (toWeights.Fp - kapW X) z ξ

end

end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
