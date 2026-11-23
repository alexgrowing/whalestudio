import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationIndep
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_presentation_indep : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ), Presents Δ L r → Presents Δ L' r' → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) L'), φ.IsCInf → ψ.IsCInf → φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_presents | exact GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_presents | (intros; apply GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_presents <;> assumption)
