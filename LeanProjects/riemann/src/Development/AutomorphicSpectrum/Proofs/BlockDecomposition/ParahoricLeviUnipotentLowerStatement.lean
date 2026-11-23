import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricLeviUnipotentLower
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_levi_unipotent_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ m ∈ (Gx k e).comap (leviEmb k e), ∃ x ∈ unipRad k e, ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx | exact GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx <;> assumption)
