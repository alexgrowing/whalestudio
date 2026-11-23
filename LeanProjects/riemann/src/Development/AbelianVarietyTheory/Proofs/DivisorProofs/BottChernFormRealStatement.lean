import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernFormReal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bott_chern_form_real : ∀ {M : Type} [TopologicalSpace M] {n r s : ℕ} (A : HolAtlas M n) (T : HermSeq A r s), A.IsRealForm 1 (bcFld T) := by
  first | exact @GlobalTheory.BcUnique.isRealForm_bcFld | exact GlobalTheory.BcUnique.isRealForm_bcFld | (intros; apply GlobalTheory.BcUnique.isRealForm_bcFld <;> assumption)
