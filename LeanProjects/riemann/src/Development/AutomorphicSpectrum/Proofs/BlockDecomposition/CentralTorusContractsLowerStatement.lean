import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLower
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_torus_contracts_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | exact GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract <;> assumption)
