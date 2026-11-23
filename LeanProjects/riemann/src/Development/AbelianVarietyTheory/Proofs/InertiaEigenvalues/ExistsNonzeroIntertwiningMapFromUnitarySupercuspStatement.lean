import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroIntertwiningMapFromUnitarySupercusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_intertwiningMap_from_unitary_supercuspidal : ∀ (G W V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G W) (ρ : Representation ℂ G V) (p : π.IntertwiningMap ρ), IsSmooth π → IsSupercuspidal ρ → IsUnitarisable ρ → (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ∀ w, π z w = c • w) → p ≠ 0 → ∃ ι : ρ.IntertwiningMap π, ι ≠ 0 := by
  first | exact @GlobalTheory.CuspBack.exists_back | exact GlobalTheory.CuspBack.exists_back | (intros; apply GlobalTheory.CuspBack.exists_back <;> assumption)
