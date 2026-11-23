import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ParahoricOpenCompact

theorem KOne_le_parahoric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] :
    KOne k (A ⊕ D) ≤ parahoric k A D := by
  intro g hg
  refine mem_parahoric.2 ⟨StepData.KOne_le_KO hg, fun i j => ?_⟩
  have h := StepData.mem_KOne.1 hg
  have h' : valuation k ((g.val - 1) (.inr i) (.inl j)) < 1 := h _ _
  simpa using h'

theorem isOpen_isCompact_parahoric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) ∧ IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  intro k _ _ _ _ A D _ _ _ _
  have ho : IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) :=
    Subgroup.isOpen_mono (KOne_le_parahoric k A D) StepData.isOpen_KOne
  exact ⟨ho, SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho)
    fun _ hg => (mem_parahoric.1 hg).1⟩

end GlobalTheory.ParahoricOpenCompact
