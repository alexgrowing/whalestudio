import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexIntegralMatricesInSubstitutionImage
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_integralMatrices_in_substitution_image : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), Enl gk hk → ∃ R₀ : Finset (Matrix Y Y' k), (R₀.card : ℝ) = nabs k (Matrix.GeneralLinearGroup.det hk) ^ (Fintype.card Y' : ℝ) * nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card Y : ℝ)) ∧ (∀ v ∈ R₀, ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * v * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]) ∧ ∀ w : Matrix Y Y' k, (∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]) → ∃! v, v ∈ R₀ ∧ ∀ r q, (w - v) r q ∈ 𝒪[k] := by
  first | exact @GlobalTheory.LocOm.IntIndex.index_integral_image | exact GlobalTheory.LocOm.IntIndex.index_integral_image | (intros; apply GlobalTheory.LocOm.IntIndex.index_integral_image <;> assumption)
