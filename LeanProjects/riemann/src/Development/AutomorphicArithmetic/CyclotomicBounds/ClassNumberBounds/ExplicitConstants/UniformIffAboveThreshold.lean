import Mathlib

open Filter Set

namespace KStar.Consta

structure Params where

  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52

  Ct : ℝ
  Ct_nonneg : 0 ≤ Ct

  Cc : ℝ

  q : ℕ
  q_pos : 0 < q

  K : ℝ
  one_le_K : 1 ≤ K

noncomputable instance : Inhabited Params :=
  ⟨{ eps := 1 / 100, eps_pos := by norm_num, eps_lt := by norm_num, Ct := 401,
     Ct_nonneg := by norm_num, Cc := 1, q := 1, q_pos := one_pos, K := 1, one_le_K := le_rfl }⟩

def jG : ℕ := 5

def Aexp : ℕ := 26

namespace Params

variable (P : Params)

noncomputable def h : ℝ := 2 + 8 * P.eps

noncomputable def KG : ℕ := ⌈8 * (P.h + 2) / P.eps⌉₊

noncomputable def L (x : ℝ) : ℝ := x ^ P.eps

noncomputable def Y (X : ℝ) : ℝ := X ^ (1 / P.K)

noncomputable def z (X : ℝ) : ℝ := P.Y X ^ (P.eps / 5)

noncomputable def zAlt (X : ℝ) : ℝ := X ^ (P.eps / (5 * P.K))

noncomputable def z' (X : ℝ) : ℝ := P.z X * Real.log (P.Y X) ^ 2

noncomputable def Lbar : ℝ := 1242 * P.K / P.eps

noncomputable def binaryExponentBound : ℝ := (2 : ℝ) ^ (P.Lbar + 1) + 4

noncomputable def jmax : ℕ := ⌈30 * P.K / P.eps⌉₊

noncomputable def Jeps : ℝ := 7 * P.K * ((jG : ℝ) + 1) / P.eps

noncomputable def N5 : ℕ := ⌈5 * P.K⌉₊

noncomputable def Lw (x : ℝ) : ℝ :=
  10 * (⌈(P.Ct + 4) * Real.log x⌉ : ℝ) + 2 * (P.jmax : ℝ) + 22

noncomputable def delZ (X : ℝ) : ℝ := Real.exp (-(P.z X ^ ((5 : ℝ) / 7)))

noncomputable def delX (x : ℝ) : ℝ := Real.exp (-(x ^ (P.eps / (8 * P.K))))

def Unif (p : ℝ → ℝ → Prop) : Prop :=
  ∀ᶠ X in atTop, ∀ x ∈ Icc (P.Y X) X, p X x

def UniformlyAboveThreshold (p : ℝ → ℝ → Prop) : Prop :=
  ∃ X₀ : ℝ, ∀ X, X₀ ≤ X → ∀ x, X ^ (1 / P.K) ≤ x → x ≤ X → p X x

theorem uniform_iff_above_threshold (p : ℝ → ℝ → Prop) : P.Unif p ↔ P.UniformlyAboveThreshold p := by
  simp only [Unif, UniformlyAboveThreshold, eventually_atTop, ge_iff_le, mem_Icc, and_imp, Y]

theorem Unif.mono {P : Params} {p r : ℝ → ℝ → Prop} (hp : P.Unif p)
    (h : ∀ X x, x ∈ Icc (P.Y X) X → p X x → r X x) : P.Unif r :=
  Filter.Eventually.mono hp fun X hX x hx => h X x hx (hX x hx)

theorem Unif.and {P : Params} {p r : ℝ → ℝ → Prop} (hp : P.Unif p) (hr : P.Unif r) :
    P.Unif fun X x => p X x ∧ r X x :=
  (Filter.Eventually.and hp hr).mono fun _ hX x hx => ⟨hX.1 x hx, hX.2 x hx⟩

theorem Unif.of_eventually_X {P : Params} {p : ℝ → Prop} (hp : ∀ᶠ X in atTop, p X) :
    P.Unif fun X _ => p X :=
  hp.mono fun _ hX _ _ => hX

structure PairSize (X : ℝ) (q₁ d : ℕ) : Prop where
  q₁_lower : P.z X / 2 < Real.log q₁
  q₁_upper : Real.log q₁ ≤ P.z X
  d_lower : P.z' X / 2 < Real.log d
  d_upper : Real.log d ≤ P.z' X
  sqrt_d : Real.exp (P.z X) ≤ Real.sqrt d

end Params

def SplitsIn (d p : ℕ) : Prop :=
  ∃ a b : ZMod p, a ≠ b ∧ a ^ 2 - a + (((1 + d) / 4 : ℕ) : ZMod p) = 0 ∧
    b ^ 2 - b + (((1 + d) / 4 : ℕ) : ZMod p) = 0

def SplitsIn' (d p : ℕ) : Prop :=
  if p = 2 then d % 8 = 7 else ¬ p ∣ d ∧ IsSquare (-(d : ZMod p))

noncomputable def oddPrimorial (w : ℝ) : ℕ :=
  ∏ p ∈ (Finset.Icc 3 ⌊w⌋₊).filter Nat.Prime, p

structure Params.WindowPair (P : Params) (X : ℝ) (q₁ d : ℕ) : Prop
    extends P.PairSize X q₁ d where
  q₁_prime : q₁.Prime
  d_prime : d.Prime
  q₁_mod : q₁ % 8 = 3
  d_mod : d % 16 = 7
  z_ge : max 60 (max (4 * P.Cc) (4 * (P.q : ℝ) + 8)) ≤ P.z X
  q₁_splits : SplitsIn d q₁
  small_splits : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ P.z X → SplitsIn d p

structure Params.CongPair (P : Params) (X : ℝ) (q₁ d : ℕ) : Prop
    extends P.PairSize X q₁ d where
  q₁_prime : q₁.Prime
  d_prime : d.Prime
  q₁_mod : q₁ % 8 = 3
  d_mod : d % 16 = 7
  cong : q₁ * oddPrimorial (P.z X) ∣ d + 1

end KStar.Consta
