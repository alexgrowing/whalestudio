import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def StepTwo.Piece.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (N₀ N₁ : FinGradedSub (S := S) (x := x) E) (g : E) (e : ℤ)
    (pp : Ideal (Poly S N)), pp.IsPrime → (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) →
    primeOf (S := S) x ≤ pp → g ∈ N₁.piece e →
    (∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g}) →
    (∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d))) →
    ∀ (Q : LineBundle S x) (c : ℤ),
      ((∃ j, (X j : Poly S N) ∉ pp) →
        Subsingleton (SubSystem.quotH (Q.twist (twistSys S x (c - e)))
          ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) 1)) →
      Subsingleton (SubSystem.quotH ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c)))
        ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c))) 1)

section Hypotheses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

variable (S x E) in

def FinGradedSub.zero : FinGradedSub (S := S) (x := x) E where
  piece _ := ⊥
  smul_mem _ _ _ m _ hm := by
    rw [Submodule.mem_bot] at hm ⊢
    rw [hm, smul_zero]
  fg := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun _ => bot_le⟩

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
