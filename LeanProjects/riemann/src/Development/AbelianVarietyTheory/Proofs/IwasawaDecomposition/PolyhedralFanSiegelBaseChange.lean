import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBoundaryPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyRefinedFanPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyPolarizationAmpleStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory

namespace GlobalTheory.SiegLoc

theorem exists_siegel_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (φ φs : InvFun ℤ) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F), 1 ≤ D.p + D.q → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → SiegAt (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n → 3 ≤ n → Odd n → n ∣ l.M → AgreesPsd (Module.finrank ℚ E / 2 * (D.p + D.q)) φs φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → ∃ C : Model Xo c ω, HasCones (ConeZ E φs) C ∧ PolRay (comb 0 (resInt _ φs) 0 (resInt _ φs)) (resInt _ φs) 1 C := by
  intro E _ _ _ H D l Xo c φ φs n R _ b ω hpq hφ hS h3 hodd hn hφs hω hωb hloc
  obtain ⟨F, S, s, j, hj, G, hG, e, BD, d, N, hD⟩ := (siegAt_iff _ _ _).1 hS
  obtain ⟨κ, C, π, hκ, hC⟩ := GlobalTheory.T.siegel_family_boundary_pullback E H D l Xo c n R b ω φ F S s j G e BD d N hpq h3 hodd hn hω hωb hloc hD
  exact ⟨C, GlobalTheory.T.siegel_family_refined_fan_pullback E H D l Xo c n R b ω φ φs F S s j G e BD d N κ C π hpq h3 hodd hn hφ hφs hω hωb hloc hD hκ hC,
    GlobalTheory.T.siegel_family_polarization_ample E H D l Xo c n R b ω φ φs F S s j G e BD d N κ C π hpq h3 hodd hn hφ hφs hω hωb hloc hD hκ hC⟩

end GlobalTheory.SiegLoc
