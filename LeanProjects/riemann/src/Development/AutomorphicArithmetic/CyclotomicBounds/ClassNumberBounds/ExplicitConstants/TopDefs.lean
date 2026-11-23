import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.UniformIffAboveThreshold

open Filter Set Real

namespace KStar.Consta

structure TopParams where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  Ct : ℝ
  Ct_nonneg : 0 ≤ Ct
  Cc : ℝ
  la : ℝ
  one_lt_la : 1 < la
  q : ℕ
  q_pos : 0 < q
  R : ℕ
  CK : ℝ
  eps_le : eps ≤ 2 * CK * Ct

noncomputable instance : Inhabited TopParams :=
  ⟨{ eps := 1 / 100, eps_pos := by norm_num, eps_lt := by norm_num, Ct := 401,
     Ct_nonneg := by norm_num, Cc := 1, la := 2, one_lt_la := by norm_num, q := 1,
     q_pos := one_pos, R := 1, CK := 1, eps_le := by norm_num }⟩

namespace TopParams

variable (T : TopParams)

noncomputable def B0 : ℝ := 2 * T.CK * T.Ct / T.eps

noncomputable def KW : ℝ := T.la ^ (T.R + 2) * T.B0 ^ T.R

theorem one_le_B0 : 1 ≤ T.B0 := (one_le_div T.eps_pos).2 T.eps_le

theorem one_le_KW : 1 ≤ T.KW :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ T.one_lt_la.le) (one_le_pow₀ T.one_le_B0)

noncomputable def toParams : Params :=
  { eps := T.eps, eps_pos := T.eps_pos, eps_lt := T.eps_lt, Ct := T.Ct,
    Ct_nonneg := T.Ct_nonneg, Cc := T.Cc, q := T.q, q_pos := T.q_pos, K := T.KW,
    one_le_K := T.one_le_KW }

noncomputable def deW : ℝ := (T.la - 1) / (T.la + 1)

end TopParams

noncomputable def Params.nAt (P : Params) (x : ℝ) : ℕ := 2 ^ ⌈Real.logb 2 (x ^ P.h)⌉₊

def Params.WindowTop (P : Params) (G : ℝ → ℝ) (θ la : ℝ) : Prop :=
  ∀ᶠ X in atTop, ∃ W : ℝ, P.Y X ≤ W ∧ W ^ la ≤ X ∧ ∀ x ∈ Icc W (W ^ la), G x ≤ x ^ θ

def LocalOsc (S : Set ℂ) (G : ℝ → ℝ) (θ la : ℝ) : Prop :=
  (∃ s ∈ S, θ < s.re) → ∀ᶠ W in atTop, ∃ y ∈ Icc W (W ^ la), y ^ θ < G y

def zeroSet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Set ℂ :=
  {s | (χ ≠ 1 ∨ s ≠ 1) ∧ χ.LFunction s = 0}

end KStar.Consta
