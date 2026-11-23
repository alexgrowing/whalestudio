import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormalOpenSubgroupCompact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.LatticeUnfoldingLerayVolume
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_open_subgroup_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) → ∃ K₁ : Subgroup (GL (Fin n) k), K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n) ∧ IsOpen (K₁ : Set (GL (Fin n) k)) ∧ (K₁ : Set (GL (Fin n) k)) ⊆ U ∧ K₁.relIndex (GlobalTheory.SplitWeil.KO k (Fin n)) ≠ 0 ∧ ∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  first | exact @GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | exact GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | (intros; apply GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO <;> assumption)
