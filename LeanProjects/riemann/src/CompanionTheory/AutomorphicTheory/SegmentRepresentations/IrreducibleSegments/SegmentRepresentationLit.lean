import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published

namespace CompanionTheory.Lit1.SegRep

set_option synthInstance.maxHeartbeats 400000 in

def SegmentRepresentationLit : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d l : ℕ), 0 < d → 0 < l → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ Z : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        Z.toSubmodule = ⨆ (S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
            (_ : S.toRepresentation.IsIrreducible), S.toSubmodule ∧
        Z.toRepresentation.IsIrreducible ∧
        HasFiniteLength (jac (consecBlocks l d) Z.toRepresentation) ∧
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
          (τ : Representation ℂ (Levi k (fun _ : Fin l => Fin d)) W), τ.IsIrreducible →
          jhMult τ (jac (consecBlocks l d) Z.toRepresentation) = jhMult τ (piTensor (segTerm σ.ρ l))

end CompanionTheory.Lit1.SegRep

end
