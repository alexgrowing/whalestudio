import Mathlib

namespace Formalism.RankGapBounds.LocalQuadraticParts

open Finset

abbrev Hgrp (e : ℕ) := (ZMod (4 * 2 ^ e))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (4 * 2 ^ e))ˣ)

def hOf (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Hgrp e :=
  QuotientGroup.mk (ZMod.unitOfCoprime l hl)

def OrdersIff : Prop :=
  ∀ (e j l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)), j ≤ e →
    ((hOf e l hl) ^ (2 ^ j) = 1 ↔
      ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1))

def OrdersBound : Prop :=
  ∀ (e J l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)), 1 ≤ J → 1 < l →
    orderOf (hOf e l hl) ≤ J → (4 * 2 ^ e : ℝ) / J - 1 ≤ l

def OrdersSumSq : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J →
    (∀ l ∈ s, l.Prime ∧ l ≠ 2 ∧ ∃ hl : Nat.Coprime l (4 * 2 ^ e), orderOf (hOf e l hl) ≤ J) →
    ∑ l ∈ s, Real.log l / (l : ℝ) ^ 2 ≤ C * J ^ 2 * Real.log (2 ^ e) / ((2 : ℝ) ^ e) ^ 2

def OrdersSumY : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (Y : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
    (∀ l ∈ s, l.Prime ∧ l ≠ 2 ∧ (l : ℝ) ≤ Y ∧
      ∃ hl : Nat.Coprime l (4 * 2 ^ e), orderOf (hOf e l hl) ≤ J) →
    ∑ l ∈ s, Real.log l / (l : ℝ) ≤ C * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e

noncomputable def wt {α : Type*} [Fintype α] (δ : ℝ) (T : Finset α) : ℝ :=
  δ ^ T.card * (1 - δ) ^ (Fintype.card α - T.card)

def RandomSubsetAvoidsBadEvents : Prop :=
  ∀ (α ι : Type) [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)],
    0 < δ → δ ≤ 1 → 0 ≤ β → (∀ p, 0 ≤ ω p) →
    (∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T), wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ p, ω p

def RandomSubsetCounterexample : Prop := ¬ RandomSubsetAvoidsBadEvents

def TopsFixed : Prop :=
  ∀ (α ι : Type) [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)],
    0 < δ → δ ≤ 1 → 6 ≤ δ * Fintype.card α → 0 ≤ β → (∀ p, 0 ≤ ω p) →
    (∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T), wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ p, ω p

end Formalism.RankGapBounds.LocalQuadraticParts
