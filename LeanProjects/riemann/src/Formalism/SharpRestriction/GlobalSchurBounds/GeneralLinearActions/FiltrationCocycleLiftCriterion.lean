import Mathlib
import Formalism.LocalRingCardinality.DataParams₂

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory

open Formalism.BasicNotions

abbrev abelian₂ (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)

def logDerivativeAtOne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

def G (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, abelian₂ n * max (y / n - 1) 0) -
    y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def sumLamChi {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N) * ((max (y / n - 1) 0 : ℝ) : ℂ)

open Classical in

def gChi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then ((G y : ℝ) : ℂ) else sumLamChi χ y + (y : ℂ) * logDerivativeAtOne χ

open Classical in

def psi0 {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N)) - (if χ = 1 then (u : ℂ) else 0)

def cn (x : ℝ) (n : ℕ) : ℝ := abelian₂ n * min 1 (x / n)

def zz (x : ℝ) : ℝ := x ^ (400 : ℕ)

def X1 (x eps : ℝ) : ℝ := Real.exp (x ^ (eps / 5))

def X2 (x eps : ℝ) : ℝ := Real.exp (x ^ (eps / 5) * Real.log x ^ 2)

def IsRealChar {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := ∀ a : ZMod N, (χ a).im = 0

def GoodFor (Q : ℝ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ IsRealChar χ ∧ (N : ℝ) ≤ Q ∧
    ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0

def Induces {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  χ.IsPrimitive ∧ ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = f a

def kron2 (D : ℤ) : ℤ := if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1

def kronSym (D : ℤ) (n : ℕ) : ℤ :=
  jacobiSym D (n / 2 ^ n.factorization 2) * kron2 D ^ n.factorization 2

def kron (D : ℤ) (a : ℕ) : ℂ := (kronSym D a : ℂ)

def chDir (d : ℕ) : ℕ → ℂ := kron (-(d : ℤ))

def psDir (q : ℕ) : ℕ → ℂ := kron (-(q : ℤ))

def chi8 : ℕ → ℂ := kron 2

def chi0 (q d : ℕ) : Fin 4 → ℕ → ℂ
  | 0 => fun _ => 1
  | 1 => chDir d
  | 2 => psDir q
  | 3 => fun a => chDir d a * psDir q a

def IsCharE (n q d : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ ∃ (i : Fin 4) (ξ : DirichletCharacter ℂ (4 * n)), ξ.Even ∧
    ∀ a : ℕ, a.Coprime (4 * n * q * d) → χ (a : ZMod N) = chi0 q d i a * ξ (a : ZMod (4 * n))

def IsCharED (D : D7) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ ∃ ψ : D.R.GG →* ℂˣ, ∀ (a : ℕ) (h : a.Coprime D.host.condN),
    χ (a : ZMod N) = ((ψ (D.host.art (ZMod.unitOfCoprime a h)) : ℂˣ) : ℂ)

def oddQS (D : D7) : ℕ := ordCompl[2] D.host.QS

def BoxE (D : D7) (x eps : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ → IsRealChar χ →
    (D.host.d ∣ N → GoodFor (8 * (oddQS D : ℝ) * X1 x eps * X2 x eps) χ) ∧
    (D.host.q ∣ N → ¬ D.host.d ∣ N → GoodFor (8 * (oddQS D : ℝ) * X1 x eps) χ)

def NE (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d

def TailSum {N : ℕ} (χ : DirichletCharacter ℂ N) (z : ℝ) (S : ℂ) : Prop :=
  Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ioc ⌊z⌋₊ M, (abelian₂ n : ℂ) * χ (n : ZMod N) / n)
    Filter.atTop (nhds S)

theorem G_eq_Gfun (y : ℝ) : G y = Gfun y := by
  unfold G Gfun
  have hs : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, abelian₂ n * max (y / n - 1) 0) =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * (y / n - 1) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hny⟩ := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hle : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).mp hny
    have h0 : 0 ≤ y / n - 1 := by
      rw [sub_nonneg, le_div_iff₀ hnpos, one_mul]
      exact hle
    rw [max_eq_left h0]
  rw [hs]
  ring

end Formalism.MainNotions.GlobalTheoryTheory

end
