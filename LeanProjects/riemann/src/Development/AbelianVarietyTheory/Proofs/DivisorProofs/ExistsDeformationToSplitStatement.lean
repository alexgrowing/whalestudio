import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationToSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deformation_to_split : ∀ {M : Type} [TopologicalSpace M] {n r s : ℕ} (A : HolAtlas M n) (T : HermSeq A r s), IsInduced T → ∃ (T' : HermSeq (famAtlas A) r s) (T₀ : HermSeq A r s), T₀.IsSplit ∧ T.IsPull T' (fib ∞) ∧ T₀.IsPull T' (fib ((0 : ℂ) : OnePoint ℂ)) ∧ IsInduced T' := by
  first | exact @GlobalTheory.BcUnique.exists_deformation | exact GlobalTheory.BcUnique.exists_deformation | (intros; apply GlobalTheory.BcUnique.exists_deformation <;> assumption)
