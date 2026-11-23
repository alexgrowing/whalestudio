import Mathlib

open Finset

noncomputable section

namespace Formalism.K

section Gauss
variable {M : Type*} [AddCommGroup M]

def polar (Q : M → ℂ) (x y : M) : ℂ :=
  Q (x + y) * (starRingEnd ℂ) (Q x) * (starRingEnd ℂ) (Q y)

structure IsUQuad (Q : M → ℂ) : Prop where
  norm_eq : ∀ x, ‖Q x‖ = 1
  neg : ∀ x, Q (-x) = Q x
  polar_add : ∀ x x' y, polar Q (x + x') y = polar Q x y * polar Q x' y

def Nondeg (Q : M → ℂ) : Prop := ∀ y, (∀ x, polar Q x y = 1) → y = 0

def gsum [Fintype M] (Q : M → ℂ) : ℂ := ∑ x, Q x

def prim (p : ℕ) : AddSubgroup M where
  carrier := {x | ∃ k : ℕ, p ^ k • x = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have h1 : (p ^ (a + b)) • x = 0 := by rw [pow_add, mul_comm (p ^ a), mul_smul, ha, smul_zero]
    have h2 : (p ^ (a + b)) • y = 0 := by rw [pow_add, mul_smul, hb, smul_zero]
    rw [smul_add, h1, h2, add_zero]
  neg_mem' := by
    rintro x ⟨k, hk⟩
    exact ⟨k, by rw [smul_neg, hk, neg_zero]⟩

end Gauss

def GaussAbs : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (Q : M → ℂ), IsUQuad Q →
    (Nondeg Q ↔ ‖gsum Q‖ ^ 2 = (Fintype.card M : ℝ))

def QuadraticGaussSumSign : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (Q : M → ℂ) (l : ℕ) (σ : AddMonoid.End M),
    l.Prime → l % 4 = 1 → IsUQuad Q → Nondeg Q →
    (∀ x, Q (σ x) = Q x) → (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    (∀ p : ℕ, p.Prime → p ≠ l → IsSquare (Nat.card (prim (M := M) p))) →
    gsum Q ^ 2 = (Fintype.card M : ℂ)

def DetSign : Prop :=
  ∀ (S : Type) [Fintype S] (n : ℕ) (γ : S → Matrix (Fin n) (Fin n) ℂ),
    (∀ k, γ k ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ k, (1 - (γ k)⁻¹).det ≠ 0) →
    (((‖∏ k, (1 - (γ k)⁻¹).det‖ : ℝ) : ℂ) / (∏ k, (1 - (γ k)⁻¹).det)) ^ 2
      = (-1) ^ (n * Fintype.card S) * ∏ k, (γ k).det

def SquareClassUnitaryProduct : Prop :=
  ∀ (S : Type) [Fintype S] (n : ℕ) (γ : S → Matrix (Fin n) (Fin n) ℂ),
    (∀ k, γ k ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ k, (1 - (γ k)⁻¹).det ≠ 0) →
    Even (Fintype.card S) →
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (Q : M → ℂ) (l : ℕ) (σ : AddMonoid.End M),
    l.Prime → l % 4 = 1 → IsUQuad Q → Nondeg Q →
    (∀ x, Q (σ x) = Q x) → (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    (∀ p : ℕ, p.Prime → p ≠ l → IsSquare (Nat.card (prim (M := M) p))) →
    ((((‖∏ k, (1 - (γ k)⁻¹).det‖ : ℝ) : ℂ) / (∏ k, (1 - (γ k)⁻¹).det))
        * (gsum Q / ((Real.sqrt (Fintype.card M) : ℝ) : ℂ))) ^ 2
      = ∏ k, (γ k).det

section Alpha
variable {L : Type*} [AddCommGroup L]

def qRef (ψ : L →+ L →+ ZMod 2) (σ : AddMonoid.End L) (l : ℕ) (x : L) : ZMod 2 :=
  ∑ i ∈ range l, ∑ j ∈ Ico (i + 1) l, ψ ((σ ^ i) x) ((σ ^ j) x)

end Alpha

def AlphaRefine : Prop :=
  ∀ (L : Type) [AddCommGroup L] (ψ : L →+ L →+ ZMod 2) (σ : AddMonoid.End L) (l : ℕ),
    Odd l → (∀ x, ψ x x = 0) → (∀ x y, ψ (σ x) (σ y) = ψ x y) →
    (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    (∀ x y, qRef ψ σ l (x + y) = qRef ψ σ l x + qRef ψ σ l y + ψ x y) ∧
    (∀ x, qRef ψ σ l (σ x) = qRef ψ σ l x)

def AlphaUnique : Prop :=
  ∀ (L : Type) [AddCommGroup L] (ψ : L →+ L →+ ZMod 2) (σ : AddMonoid.End L) (l : ℕ),
    Odd l → (∀ x, ψ x x = 0) → (∀ x y, ψ (σ x) (σ y) = ψ x y) →
    (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    ∀ q' : L → ZMod 2, (∀ x y, q' (x + y) = q' x + q' y + ψ x y) → (∀ x, q' (σ x) = q' x) →
      q' = qRef ψ σ l

def AlphaInv : Prop :=
  ∀ (L : Type) [AddCommGroup L] (ψ : L →+ L →+ ZMod 2) (σ : AddMonoid.End L) (l : ℕ),
    Odd l → (∀ x, ψ x x = 0) → (∀ x y, ψ (σ x) (σ y) = ψ x y) →
    (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    ∀ γ : AddMonoid.End L, (∀ x, γ (σ x) = σ (γ x)) → (∀ x y, ψ (γ x) (γ y) = ψ x y) →
      ∀ x, qRef ψ σ l (γ x) = qRef ψ σ l x

end Formalism.K
