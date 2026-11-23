import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernIsHomogeneousCmType
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_isHomogeneous_cmType : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), (rootDiscr Dw.mult).IsHomogeneous (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2)) := by
  first | exact @GlobalTheory.GrassTop.rootDiscr_isHomogeneous | exact GlobalTheory.GrassTop.rootDiscr_isHomogeneous | (intros; apply GlobalTheory.GrassTop.rootDiscr_isHomogeneous <;> assumption)
