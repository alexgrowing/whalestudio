import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ExtTensorIrr

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem piTensor_isIrreducible : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β]
    (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k)),
    (GlobalTheory.SmGL.piTensor fun j => (s j).ρ).IsIrreducible := by
  intro hBZ k _ _ _ _ β _ c _ _ s
  obtain ⟨hAdm, -, -, -⟩ := hBZ k
  exact GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur (fun j => (s j).ρ) (fun j => (s j).irr)
    fun j φ hφ => GlobalTheory.SchurAdm.schur_admissible (GL (c j) k) (KO k (c j)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO (s j).V (s j).ρ (s j).irr
      (hAdm (c j) (s j).V (s j).ρ (s j).smooth (s j).irr) φ hφ

end GlobalTheory.ExtTensorIrr
