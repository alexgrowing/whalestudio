import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernFormPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bott_chern_form_pullback : ∀ {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' r s : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n') (T : HermSeq A r s) (T' : HermSeq A' r s) (f : M' → M), A.IsHolo A' f → T'.IsPull T f → bcFld T' = A.pullback A' f (bcFld T) := by
  first | exact @GlobalTheory.BcUnique.bcFld_isPull | exact GlobalTheory.BcUnique.bcFld_isPull | (intros; apply GlobalTheory.BcUnique.bcFld_isPull <;> assumption)
