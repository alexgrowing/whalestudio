import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineDomainPreimageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsOnOpenPullStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDualNumberPointsFrameStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

namespace GlobalTheory.ChartDown

theorem chart_down : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X), IsOpenImmersion v → Nonempty (SABMap Y'.t Y.t v) → ∀ (M : MChart Y) (y : Y'.X), v y ∈ M.U → ∃ M' : MChart Y', y ∈ M'.U := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' v hv ⟨n⟩ M y hy
  obtain ⟨U', hU', hd, hyU, hle⟩ := GlobalTheory.T.exists_affine_domain_preimage v hv M.U M.hU M.dom y hy
  obtain ⟨θ, hθ, hne⟩ := GlobalTheory.T.exists_sections_on_open_pull Y Y' v n M U' hle
  obtain ⟨k, v₀, ρ, hl⟩ := GlobalTheory.T.exists_dual_number_points_frame Y Y' v n M U' hU' hle
  exact ⟨⟨U', hU', hd, θ, hθ, hne, k, v₀, ρ, hl⟩, hyU⟩

end GlobalTheory.ChartDown
