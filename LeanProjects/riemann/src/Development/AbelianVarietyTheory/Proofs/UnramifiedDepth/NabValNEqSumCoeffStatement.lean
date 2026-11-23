import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNEqSumCoeff
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_nabValN_eq_sum_coeff_mul_monomial : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (P : MvPolynomial ι K), ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ f : PS K n d, nabValN B K h w0 m f cp u P = ∑ μ ∈ S, MvPowerSeries.coeff μ f * nabValN B K h w0 m (MvPowerSeries.monomial μ (1 : K)) cp u P := by
  first | exact @GlobalTheory.nabValN_eq_sum_coeff | exact GlobalTheory.nabValN_eq_sum_coeff | (intros; apply GlobalTheory.nabValN_eq_sum_coeff <;> assumption)
