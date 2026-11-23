import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsSubspacesContaining
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_integralIndicator_cosets_subspaces_containing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = (Nat.card {U : Submodule 𝓀[k] (D' → 𝓀[k]) // LinearMap.range (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ≤ U ∧ Module.finrank 𝓀[k] U + s.card = Fintype.card D'} : ℂ) := by
  first | exact @GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up | exact GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up | (intros; apply GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up <;> assumption)
