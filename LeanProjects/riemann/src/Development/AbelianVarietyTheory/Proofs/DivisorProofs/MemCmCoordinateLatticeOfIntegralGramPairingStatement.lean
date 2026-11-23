import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCmCoordinateLatticeOfIntegralGramPairing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cmCoordinateLattice_of_integral_gramPairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  first | exact @GlobalTheory.FlatCM.HomLat.mem_lat_of_dual | exact GlobalTheory.FlatCM.HomLat.mem_lat_of_dual | (intros; apply GlobalTheory.FlatCM.HomLat.mem_lat_of_dual <;> assumption)
