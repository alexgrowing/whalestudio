import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelVerticalLettersSetup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_model_vertical_letters_setup : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B₁ B : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B B₁) (h₁ : B₁.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (lw oo : EPres B₁ (𝓞 E)), IsHTPair Z h₁ x lw oo → ∃ lw' oo' : EPres B (𝓞 E), IsHTPair Z (g.f ≫ h₁) x lw' oo' := by
  first | exact @GlobalTheory.ChainPts.PullHT.isHTPair_pull | exact GlobalTheory.ChainPts.PullHT.isHTPair_pull | (intros; apply GlobalTheory.ChainPts.PullHT.isHTPair_pull <;> assumption)
