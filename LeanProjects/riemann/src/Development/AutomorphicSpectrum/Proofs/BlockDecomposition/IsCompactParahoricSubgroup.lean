import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

theorem isCompact_Gx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), IsCompact (Gx k e : Set (GL (Fin n) k)) := by
  intro k _ _ _ _ n s d e
  have hle : PositivityTheory.LowerBoundConstant.Gx k e ≤ GlobalTheory.SplitWeil.KO k (Fin n) := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact sup_le GlobalTheory.StepData.KOne_le_KO inf_le_right
  have hopen : IsOpen (PositivityTheory.LowerBoundConstant.Gx k e : Set (GL (Fin n) k)) := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact Subgroup.isOpen_mono le_sup_left GlobalTheory.StepData.isOpen_KOne
  exact GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ hopen) (fun x hx => hle hx)

end GlobalTheory.CompanionTheory.MoyPrasad
