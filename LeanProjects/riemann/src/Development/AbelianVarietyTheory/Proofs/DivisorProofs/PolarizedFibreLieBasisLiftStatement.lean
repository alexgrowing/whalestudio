import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedFibreLieBasisLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_fibre_lie_basis_lift : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (K'' : Type) [Field K''] [NumberField K''] [Algebra K K''] (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left), GlobalTheory.IsPolFibre (algebraMap K K'') F.P₀ P ψ → ∃ v' : Fin F.P₀.g → (epsR K'' ⟶ P.A), (∀ k, GlobalTheory.IsVecOver (algebraMap K K'') ψ (F.v k) (v' k)) ∧ IsLieBasis v' := by
  first | exact @GlobalTheory.LieHt.exists_isLieBasis_isVecOver_of_isPolFibre | exact GlobalTheory.LieHt.exists_isLieBasis_isVecOver_of_isPolFibre | (intros; apply GlobalTheory.LieHt.exists_isLieBasis_isVecOver_of_isPolFibre <;> assumption)
