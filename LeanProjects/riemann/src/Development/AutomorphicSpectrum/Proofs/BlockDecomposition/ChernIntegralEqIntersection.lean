import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralRandomSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AeZeroCountEqIntersectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.CompanionTheory.ChernDegree

theorem chernInt_fsBasis_eq_inter : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ((Y.inter fun _ => Δ : ℤ) : ℝ) := by
  intro Y Δ L r hL n b hb hP
  obtain ⟨μ, hμ, hac, heq⟩ := GlobalTheory.T.chern_integral_random_sections Y Δ L r hL n b hb hP
  rw [heq, integral_congr_ae (g := fun _ => (((Y.inter fun _ => Δ : ℤ)) : ℝ)) ?_]
  · simp
  · filter_upwards [hac.ae_le (GlobalTheory.T.ae_zero_count_eq_intersection Y Δ L r hL n b hb hP)] with C hC
    exact_mod_cast hC

end GlobalTheory.CompanionTheory.ChernDegree
