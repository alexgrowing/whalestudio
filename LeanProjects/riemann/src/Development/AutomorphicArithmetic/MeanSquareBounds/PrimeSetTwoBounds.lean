import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
import Formalism.PeriodIntegrals.ExplicitFormula

open Finset
open Formalism.HermitianLattices.ZeroFreeRegionGL2

noncomputable section

namespace QH

def S (Z y : ℝ) (q : ℕ) (κ : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊Z⌋₊, ((cN y n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)

def J (q n : ℕ) : ℂ := ((jacobiSym (n : ℤ) q : ℤ) : ℂ)

structure admitted (ε Y U : ℝ) (m₀ a₀ : ℕ) : Prop where
  pos : 0 < m₀
  eight : 8 ∣ m₀
  coprime : a₀.Coprime m₀
  log_m : (1 / 4) * Real.log Y ^ 2 * Real.log m₀ ≤ Real.log U
  lo : Y ^ (ε / 6) ≤ Real.log U
  hi : Real.log U ≤ Y ^ (ε / 5) * Real.log Y ^ 2

def MeanSq (C Z : ℝ) (P : Finset ℕ) (A : Set ℝ) : Prop :=
  ∀ y ∈ A, ∀ κ : ℕ → ℂ, (∀ n, ‖κ n‖ ≤ 1) → ∑ q ∈ P, ‖S Z y q κ‖ ^ 2 ≤ C * y * Real.log y * P.card

def Ind {N : ℕ} (ψ : DirichletCharacter ℂ N) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ψ.IsPrimitive ∧ ∀ n : ℕ, n.Coprime M → ψ (n : ZMod N) = f n

def GoodC (Q : ℝ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : Prop :=
  ψ ≠ 1 ∧ (N : ℝ) ≤ Q ∧ ZeroFreeBox Q ψ

def Box (Q C τ Y X : ℝ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : Prop :=
  GoodC Q ψ ∧ ‖logDerivLAtOne ψ‖ ≤ C * Real.log Y ∧ ∀ y ∈ Set.Icc Y X, ‖Gchi ψ y‖ ≤ y ^ (1 / 2 + τ)

def BoxAll (Q C τ Y X : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), Ind ψ f M → Box Q C τ Y X ψ

def primePairSetFirst (z : ℝ) : Finset ℕ := PPset 8 3 (Real.exp z)

open Classical in

def primeSetTwoBounds (z z' : ℝ) (q : ℕ) : Finset ℕ :=
  (Icc 1 ⌊Real.exp z'⌋₊).filter fun d => d.Prime ∧ d % 16 = 7 ∧ oddM z q ∣ d + 1 ∧ Real.exp z' ^ (1 / 2 : ℝ) < (d : ℝ)

def GoodQ (N₀ : ℕ) (C τ Y X z : ℝ) (q : ℕ) : Prop :=
  ∀ ξ : DirichletCharacter ℂ N₀, BoxAll (N₀ * Real.exp z) C τ Y X (fun n => ξ n * J q n) (N₀ * q)

def GoodD (N₀ : ℕ) (C τ Y X z z' : ℝ) (q d : ℕ) : Prop :=
  ∀ ξ : DirichletCharacter ℂ N₀, ∀ a : ℕ, a ≤ 1 →
    BoxAll (N₀ * Real.exp (z + z')) C τ Y X (fun n => ξ n * J q n ^ a * J d n) (N₀ * q * d)

structure Rows (z z' : ℝ) (q d : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_gt : z / 2 < Real.log q
  q_le : Real.log q ≤ z
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_gt : z' / 2 < Real.log d
  d_le : Real.log d ≤ z'
  q_lt_d : q < d
  d_class : ∀ p : ℕ, p.Prime → p ≠ 2 → ((p : ℝ) ≤ z ∨ p = q) → (d + 1) % p = 0

open Classical in

def G0 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ := if χ = 1 then ((G1 y : ℝ) : ℂ) else Gchi χ y

def NoExc (c : ℝ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ β : ℝ, 1 - c < β → β < 1 → DirichletCharacter.LFunction χ β ≠ 0

end QH

end
