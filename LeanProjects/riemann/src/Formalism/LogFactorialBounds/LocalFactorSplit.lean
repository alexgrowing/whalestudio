import Mathlib

noncomputable section

namespace Formalism.LogFactorialBounds

open Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def CardGLForm : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ),
    (Nat.card (GL (Fin n) F) : ℝ) = (Fintype.card F : ℝ) ^ (n * n) * qE (Fintype.card F) 1 n

def blockUpper {F : Type} [Field F] (a t : ℕ) (J' : Set (GL (Fin a) F)) :
    Set (GL (Fin a ⊕ Fin t) F) :=
  {A | (∀ i j, (A : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) (Sum.inr i) (Sum.inl j) = 0) ∧
       ∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = (A : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F).toBlocks₁₁}

def CardBlockUpper : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Nat.card (blockUpper (F := F) a t (J' : Set (GL (Fin a) F))) =
      Nat.card J' * Nat.card (GL (Fin t) F) * Fintype.card F ^ (a * t)

def ParabolicIndex : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (r s : ℕ),
    (Nat.card (GL (Fin r ⊕ Fin s) F) : ℝ) / (Nat.card (blockUpper (F := F) r s Set.univ) : ℝ) =
      (Fintype.card F : ℝ) ^ (r * s) * qE (Fintype.card F) 1 (r + s) /
        (qE (Fintype.card F) 1 r * qE (Fintype.card F) 1 s)

def LocalFactorSplit : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    let q : ℝ := Fintype.card F
    ((Nat.card (GL (Fin a ⊕ Fin t) F) : ℝ) /
        (Nat.card (blockUpper (F := F) a t (J' : Set (GL (Fin a) F))) : ℝ)) *
      (qE q 1 (a + t))⁻¹ *
      ((Nat.card J' : ℝ) * q ^ (-((a * a : ℕ) : ℤ)) * q ^ (-((a * t : ℕ) : ℤ))) =
    (qE q 1 t)⁻¹

def LocalFactorTame : Prop :=
  ∀ (q : ℝ), 1 < q → ∀ (r t j : ℕ), 1 ≤ j → ∀ L : ℝ,
    (q ^ (r * j * t) * qE q 1 (r + j * t) / (qE q 1 r * qE q 1 (j * t))) *
        (qE q 1 (r + j * t))⁻¹ *
        (q ^ (-((j * t * r : ℕ) : ℤ)) * qE q 1 r * L / (qE q (t + 1) (j * t))⁻¹) =
      (qE q 1 t)⁻¹ * L

def LocalExponents : Prop :=
  ∀ (r j t c : ℕ) (e : Fin c → ℤ),
    let b : ℚ := r + j * t
    (-(b / 2) * ∑ i, (e i : ℚ) - b * ∑ i, (max 0 (-(e i)) : ℚ)) +
        ((r / 2 : ℚ) * ∑ i, (e i : ℚ) - r * ∑ i, (max 0 (e i) : ℚ)) +
        ((r : ℚ) * ∑ i, (max 0 (-(e i)) : ℚ) + r * ∑ i, (max 0 (e i) : ℚ)) =
      -((j * t : ℚ) / 2) * ∑ i, (|e i| : ℚ)

def HookBound : Prop :=
  ∀ (l : ℕ) (hl : 1 ≤ l) (a : Fin l → ℕ), Antitone a →
    |Real.log ((∏ i : Fin l, ((a i + (l - 1 - i.val)).factorial : ℝ)) /
        ∏ p ∈ (univ.filter fun p : Fin l × Fin l => p.1 < p.2),
          ((a p.1 - a p.2 + (p.2.val - p.1.val) : ℕ) : ℝ)) -
      ∑ i : Fin l, Real.log ((a i).factorial : ℝ)| ≤
    2 * (l : ℝ) ^ 2 * Real.log ((a ⟨0, hl⟩ : ℝ) + l)

end Formalism.LogFactorialBounds
