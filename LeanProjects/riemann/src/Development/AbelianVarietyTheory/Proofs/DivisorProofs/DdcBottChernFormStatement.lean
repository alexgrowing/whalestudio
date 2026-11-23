import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcBottChernForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_bott_chern_form : ∀ {M : Type} [TopologicalSpace M] {n r s : ℕ} (A : HolAtlas M n) (T : HermSeq A r s), IsInduced T → ∀ (a : T.κ) (x : A.Pt), x.pt ∈ T.U a → A.ddc (bcFld T) x = ((-(A.chern (T.sub a) 2 x + A.chern (T.sub a) 1 x * A.chern (T.quot a) 1 x + A.chern (T.quot a) 2 x - A.chern (T.mid a) 2 x)) : Ev n) := by
  first | exact @GlobalTheory.BcUnique.ddc_bcFld | exact GlobalTheory.BcUnique.ddc_bcFld | (intros; apply GlobalTheory.BcUnique.ddc_bcFld <;> assumption)
