import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardCmTypeEmbeddingsFixingRootEqHalfFinrank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cmTypeEmbeddingsFixingRoot_eq_half_finrank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
  first | exact @GlobalTheory.CMTypeCard.card_psi_eq_half | exact GlobalTheory.CMTypeCard.card_psi_eq_half | (intros; apply GlobalTheory.CMTypeCard.card_psi_eq_half <;> assumption)
