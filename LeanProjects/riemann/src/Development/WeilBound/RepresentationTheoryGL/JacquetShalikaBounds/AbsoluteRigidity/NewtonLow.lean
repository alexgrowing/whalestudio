import Mathlib

noncomputable section

open scoped ComplexConjugate

namespace PositivityTheory.RgJS

variable {W : Type}

def eul (q : W → ℕ) {A B : Type} [Fintype A] [Fintype B] (α : W → A → ℂ) (β : W → B → ℂ) (s : ℂ) : ℂ :=
  ∏' w, ∏ a, ∏ b, (1 - α w a * conj (β w b) * (q w : ℂ) ^ (-s))⁻¹

def lterm (q : W → ℕ) {A B : Type} [Fintype A] [Fintype B] (α : W → A → ℂ) (β : W → B → ℂ) (s : ℂ) (p : W × ℕ) : ℂ :=
  (∑ a, α p.1 a ^ (p.2 + 1)) * conj (∑ b, β p.1 b ^ (p.2 + 1)) * ((q p.1 : ℂ) ^ (-s)) ^ (p.2 + 1) / (p.2 + 1)

structure Primes (q : W → ℕ) : Prop where
  two : ∀ w, 2 ≤ q w
  conv : ∀ σ : ℝ, 1 < σ → Summable fun w => (q w : ℝ) ^ (-σ)
  div : ¬ Summable fun w => (q w : ℝ)⁻¹

open Classical in

structure Sys (q : W → ℕ) (X : Type) (d : X → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) : Prop where
  primes : Primes q
  pos : ∀ x, 1 ≤ d x
  bd : ∀ x w a, ‖A x w a‖ ≤ Real.sqrt (q w)
  det : ∀ x w, ‖∏ a, A x w a‖ = 1
  rs : ∀ x y, ∃ (F : ℂ → ℂ) (σ₀ : ℝ), (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F σ) ∧
    ∀ σ : ℝ, σ₀ < σ → F σ = (if x = y then (σ : ℂ) - 1 else 1) * eul q (A x) (A y) σ

def LandauL : Prop := ∀ (I : Type) (c l : I → ℝ) (σ₀ σ₁ : ℝ) (F : ℂ → ℂ), (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ l i) →
  (∀ σ : ℝ, σ₀ < σ → AnalyticAt ℂ F σ) → (∀ σ : ℝ, σ₁ < σ → Summable fun i => c i * Real.exp (-(l i * σ))) →
  (∀ σ : ℝ, σ₁ < σ → F σ = (Real.exp (∑' i, c i * Real.exp (-(l i * σ))) : ℝ)) →
    ∀ σ : ℝ, σ₀ < σ → Summable fun i => c i * Real.exp (-(l i * σ))

def NewtonLow : Prop := ∀ N : ℕ, 1 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (A : Type) [Fintype A] (a : A → ℂ), Fintype.card A = N →
  ‖∏ i, a i‖ = 1 → c ≤ ∑ k ∈ Finset.range N, ‖∑ i, a i ^ (k + 1)‖ ^ 2

def EulerLog : Prop := ∀ (W : Type) (q : W → ℕ) (A B : Type) [Fintype A] [Fintype B] (α : W → A → ℂ) (β : W → B → ℂ) (s : ℂ),
  Primes q → (∀ w a, ‖α w a‖ ≤ Real.sqrt (q w)) → (∀ w b, ‖β w b‖ ≤ Real.sqrt (q w)) → 2 < s.re →
    Summable (fun p => ‖lterm q α β s p‖) ∧ eul q α β s = Complex.exp (∑' p, lterm q α β s p) ∧
      Multipliable fun w => ∏ a, ∏ b, (1 - α w a * conj (β w b) * (q w : ℂ) ^ (-s))⁻¹

def Remov : Prop := ∀ (G : ℂ → ℂ) (r : ℕ) (M : ℝ), (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ) →
  (∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖G σ‖ ≤ M * (σ - 1) ^ r) →
    ∃ G' : ℂ → ℂ, (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G' σ) ∧ ∀ σ : ℝ, 1 < σ → G σ = ((σ : ℂ) - 1) ^ r * G' σ

def ForSys (Q : ∀ {W : Type} (_ : W → ℕ) {X : Type} {d : X → ℕ}, (∀ x, W → Fin (d x) → ℂ) → Prop) : Prop :=
  ∀ (W : Type) (q : W → ℕ) (X : Type) (d : X → ℕ) (A : ∀ x, W → Fin (d x) → ℂ), Sys q X d A → Q q A

def Conv1 : Prop := ForSys fun q X _ A => ∀ x y : X, (∀ σ : ℝ, 1 < σ → Summable fun p => ‖lterm q (A x) (A y) σ p‖) ∧
  ∀ σ₁ : ℝ, 1 < σ₁ → ∃ M : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ‖∑' p, lterm q (A x) (A y) σ p‖ ≤ M

def Unb : Prop := ForSys fun q X _ A => ∀ (ι : Type) [Fintype ι] [Nonempty ι] (x : ι → X),
  ¬ ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖∑ i, ∑ j, ∑' p, lterm q (A (x i)) (A (x j)) σ p‖ ≤ M

def Rel (q : W → ℕ) {X : Type} {d : X → ℕ} (A : ∀ x, W → Fin (d x) → ℂ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ) : Prop :=
  ∀ w (k : ℕ), ∑ i, ∑ a, (A (x i).1 w a * (q w : ℂ) ^ (-((x i).2 : ℂ))) ^ k =
    ∑ j, ∑ b, (A (y j).1 w b * (q w : ℂ) ^ (-((y j).2 : ℂ))) ^ k

def Common0 : Prop := ForSys fun q X _ A => ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (x : ι → X × ℝ) (y : κ → X × ℝ),
  Rel q A x y → (∀ i, 0 ≤ (x i).2) → (∀ j, 0 ≤ (y j).2) → (∃ i, (x i).2 = 0) → ∃ i j, x i = y j

def AbsRig : Prop := ForSys fun q X _ A => ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (x : ι → X × ℝ) (y : κ → X × ℝ),
  Rel q A x y → ∃ s : ι ≃ κ, ∀ i, x i = y (s i)

end PositivityTheory.RgJS
