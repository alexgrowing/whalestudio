import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantValueCopiesEqZeroOfLowCoeff
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantValueCopies_eq_zero_of_low_coeff : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  first | exact @GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero | exact GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero | (intros; apply GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero <;> assumption)
