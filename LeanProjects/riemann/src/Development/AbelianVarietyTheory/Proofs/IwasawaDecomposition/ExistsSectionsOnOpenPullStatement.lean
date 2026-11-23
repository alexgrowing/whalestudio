import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsOnOpenPull
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_on_open_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X), SABMap Y'.t Y.t v → ∀ (M : MChart Y) (U' : Y'.X.Opens), U' ≤ v ⁻¹ᵁ M.U → ∃ θ : (∀ i, Γ(Y'.t.G.left, Y'.t.G.hom ⁻¹ᵁ U' ⊓ Y'.t.PP.L.U i)), θ ∈ secOn Y'.t.PP.L (Y'.t.G.hom ⁻¹ᵁ U') ∧ ∀ y ∈ U', ∃ (g : Y'.t.G.left) (i : Y'.t.PP.L.ι), Y'.t.G.hom g = y ∧ g ∈ Y'.t.G.left.basicOpen (θ i) := by
  first | exact @GlobalTheory.ThetaPullChart.exists_theta_pull | exact GlobalTheory.ThetaPullChart.exists_theta_pull | (intros; apply GlobalTheory.ThetaPullChart.exists_theta_pull <;> assumption)
