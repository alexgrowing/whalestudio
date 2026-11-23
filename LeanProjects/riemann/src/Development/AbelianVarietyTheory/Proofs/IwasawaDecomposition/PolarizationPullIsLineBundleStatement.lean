import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationPullIsLineBundle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_pull_isLineBundle : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (m : ℕ) (DY : EffCartierData Y.X) {X' : Scheme.{0}} (F : X' ⟶ Y.X), (∀ y : X', ∃ M : MChart Y, F y ∈ M.U) → ((polOf Y m DY).pull F).IsLB := by
  first | exact @GlobalTheory.PolPull.isLB_pull_polOf | exact GlobalTheory.PolPull.isLB_pull_polOf | (intros; apply GlobalTheory.PolPull.isLB_pull_polOf <;> assumption)
