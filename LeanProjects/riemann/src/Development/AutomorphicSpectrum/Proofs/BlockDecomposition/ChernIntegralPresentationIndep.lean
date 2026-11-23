import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralWeightIndepStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationTransferStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.CompanionTheory.ChernMass

theorem chernInt_eq_of_presents (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ)
    (r' : L'.ι → Y.Fnˣ) (hL : Presents Δ L r) (hL' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) L')
    (hφ : φ.IsCInf) (hψ : ψ.IsCInf) :
    φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  obtain ⟨ψ₀, hψ₀, hmass⟩ := GlobalTheory.T.chern_integral_presentation_transfer Y Δ L L' r r' hL hL' φ hφ
  rw [← hmass]
  exact GlobalTheory.T.chern_integral_weight_indep Y L' ψ₀ ψ hψ₀ hψ

end GlobalTheory.CompanionTheory.ChernMass
