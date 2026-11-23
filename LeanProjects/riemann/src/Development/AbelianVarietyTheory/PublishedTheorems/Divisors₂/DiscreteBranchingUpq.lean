import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.Published

open GlobalTheory.SepReal

def DiscreteBranchingUpq : Prop :=
  ∀ (n : ℕ) (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool),
    1 ≤ n → Signs e ε ε' → IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H')), IsDS ε lam π →
      (∀ mu : Fin n → ℝ, IsHCParam mu → IsDS ε' mu σ →
        (Interlaced ε lam ε' mu → ∃ j P, IsProj e ε' π σ j P) ∧
        (¬ Interlaced ε lam ε' mu → ∀ j, IsHMap e ε' π σ j → j = 0)) ∧
      (CompleteSpace H' → IsURepOn (UJset ε') σ → IsIrredOn (UJset ε') σ → (∃ j, IsHMap e ε' π σ j ∧ j ≠ 0) →
        ∃ (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ), IsHCParam mu ∧ Interlaced ε lam (ε' ∘ s) mu ∧
          IsDS (ε' ∘ s) mu (fun h => σ (h.submatrix s.symm s.symm)))

theorem DiscreteBranchingUpq.occ (h : DiscreteBranchingUpq) :
    ∀ (n : ℕ) (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ),
    1 ≤ n → Signs e ε ε' → IsHCParam lam → IsHCParam mu → Interlaced ε lam ε' mu →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H')), IsDS ε lam π → IsDS ε' mu σ → ∃ j P, IsProj e ε' π σ j P :=
  fun n e ε lam ε' mu hn hs hl hm hI H H' _ _ _ _ π σ hp hσ =>
    ((h n e ε lam ε' hn hs hl H H' π σ hp).1 mu hm hσ).1 hI

end GlobalTheory.Published
