import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

section Formal

variable {R : Type*} [CommRing R]

def Uo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (l * n)

def Vo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then a (n / l) else 0

def dep (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then 0 else a n

def To (k : ℕ) (c : R) (q : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (q * n) + c * (q : R) ^ (k - 1) * Vo q a n

def mul (a b : ℕ → R) : ℕ → R := fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def eis (j : ℕ) (c : R) (a b : ℤ → R) : ℕ → R := fun n =>
  if n = 0 then c else ∑ p ∈ n.divisorsAntidiagonal, a p.1 * (p.1 : R) ^ (j - 1) * b p.2

def Zs (k l : ℕ) (u v : ℤ → R) (F : ℕ → ℕ → R) : ℕ → R := fun n =>
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ x ∈ p.1.divisorsAntidiagonal, ∑ y ∈ p.2.divisorsAntidiagonal,
    if l ∣ p.1 ∨ l ∣ p.2 then 0 else (x.1 : R) ^ (k - 2) * u x.2 * v y.1 * F x.1 y.1

def quo {M : ℕ} (f : ZMod M → R) : ℕ → ℕ → R := fun x x' => f ((x : ZMod M) * (x' : ZMod M)⁻¹)

def lam (B : ℕ) (c a : ℕ → R) : R := ∑ n ∈ Finset.range B, c n * a n

end Formal

section Level

variable {K : Type*} [Field K]

def val (B : ℕ) (c : ℕ → K) (l : ℕ) (α : K) (r : ℕ) (a : ℕ → K) : K := (α ^ r)⁻¹ * lam B c ((Uo l)^[r] a)

def Fser (j M : ℕ) (ζ : K) (b : ℤ → K) (c : K) (u w : ZMod M) : ℕ → K := fun s =>
  if s = 0 then c else ∑ p ∈ s.divisorsAntidiagonal,
    ((if (p.1 : ZMod M) = u then ((p.1 : K) / M) ^ (j - 1) * ζ ^ (w.val * p.2) * b p.2 else 0) -
      (if -(p.1 : ZMod M) = u then (-(p.1 : K) / M) ^ (j - 1) * (ζ ^ (w.val * p.2))⁻¹ * b (-(p.2 : ℤ)) else 0))

end Level

section Bridge

variable {K : Type*} [Field K] [CharZero K]

theorem mul_eq_cmul (f g : ℕ → K) : mul f g = GlobalTheory.KummerEisensteinGalois.cmul f g := by
  funext n
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f i * g j) n

end Bridge

example : eis 4 (0 : ℤ) (fun _ => 1) (fun _ => 1) 2 = 9 := by decide

example : To 12 (1 : ℤ) 2 (fun n => if n = 1 then 1 else if n = 4 then -1472 else 0) 2 = (-24) ^ 2 := by
  simp [To, Vo]

example (u v : ℤ → ℤ) (F : ℕ → ℕ → ℤ) : Zs 3 3 u v F 2 = u 1 * v 1 * F 1 1 := by
  simp [Zs, Finset.Nat.antidiagonal_succ]

def hat {N : ℕ} (φ : ZMod N → ℂ) (d : ℤ) : ℂ := ∑ y ∈ Finset.range N, φ y * cexp (2 * π * Complex.I * (y * d) / N)

def qs (a : ℕ → ℂ) (τ : ℍ) : ℂ := ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)

def PolyB (a : ℕ → ℂ) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A

def Inv (k L : ℕ) (χ : ℤ → ℂ) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ : ℍ, f (γ • τ) = χ (γ 1 1) * (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k * f τ

def MF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := PolyB a ∧ Inv k L χ (qs a)

def CF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := MF k L χ a ∧ ∃ C : ℝ, ∀ τ : ℍ, ‖qs a τ‖ ^ 2 * τ.im ^ k ≤ C

def ch {N : ℕ} (χ : DirichletCharacter ℂ N) : ℤ → ℂ := fun d => χ (d : ZMod N)

structure Prim (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) : Prop where
  cf : CF k N (ch χ) g
  one : g 1 = 1
  zero : ∀ n : ℕ, ¬ n.Coprime N → g n = 0
  eig : ∀ q : ℕ, q.Prime → ¬ q ∣ N → To k (ch χ q) q g = fun n => g q * g n

structure Wt (L : ℕ) (ρ : ℍ → ℝ) : Prop where
  meas : Measurable ρ
  nonneg : ∀ τ, 0 ≤ ρ τ
  sum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ)) • τ)) 1
  supp : ∃ S : Finset SL(2, ℤ), ∀ τ, ρ τ ≠ 0 → ∃ γ ∈ S, γ • τ ∈ ModularGroup.fd

def pet (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) : ℂ := ∫ τ : ℍ, (ρ τ : ℂ) * (conj (h τ) * f τ * (τ.im : ℂ) ^ k)

def petIP (k : ℕ) (ρ : ℍ → ℝ) (f h : ℍ → ℂ) : ℂ := ∫ τ : ℍ, 2 * (ρ τ : ℂ) * (f τ * conj (h τ) * (τ.im : ℂ) ^ k)

structure EigF (k N l : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) : Prop where
  T : ∀ a, MF k (N * l) (ch ε) a → ∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam B c (To k (ch ε q) q a) = t q * lam B c a
  U : ∀ a, MF k (N * l) (ch ε) a → lam B c (Uo l a) = α * lam B c a

def trm (j : ℕ) (s : ℝ) (z : ℂ) : ℂ := (z ^ j)⁻¹ * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ)

def dif (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) : ℤ × ℤ → ℂ := fun x =>
  F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, F (x + (r : ℤ) • v)

def lat (j : ℕ) (s : ℝ) (L : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ) : ℂ :=
  ∑' x : ℤ × ℤ, Φ x * dif L v (dif L v fun y => trm j s ((y.1 : ℂ) * τ + y.2)) x

end GlobalTheory.EisM

end
