import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLinearHomCoordinateLatticeFg
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLinearHomCoordinateLattice_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    (GlobalTheory.FlatCM.HomLat.lat X).FG := by
  first | exact @GlobalTheory.FlatCM.HomLat.lat_fg | exact GlobalTheory.FlatCM.HomLat.lat_fg | (intros; apply GlobalTheory.FlatCM.HomLat.lat_fg <;> assumption)
