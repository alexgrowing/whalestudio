import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.Published

def consecBlocks (l d : ℕ) : (Σ _ : Fin l, Fin d) ≃ Fin (l * d) :=
  (Equiv.sigmaEquivProd (Fin l) (Fin d)).trans finProdFinEquiv

theorem consecBlocks_val (l d : ℕ) (a : Fin l) (j : Fin d) : (consecBlocks l d ⟨a, j⟩ : ℕ) = j + d * a := rfl

def SegmentRepresentation : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d l : ℕ), 0 < d → 0 < l → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (consecBlocks l d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ l)))

end GlobalTheory.Published

end
