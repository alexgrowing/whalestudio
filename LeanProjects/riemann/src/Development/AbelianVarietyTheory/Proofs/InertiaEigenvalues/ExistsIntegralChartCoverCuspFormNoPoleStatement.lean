import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralChartCoverCuspFormNoPole
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_chart_cover_cuspForm_no_pole : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ (J : Type) (_ : Finite J) (P : J → GlobalTheory.Reg.PChart Xo c (algebraMap (la.valuation c.F).valuationSubring c.F)), GlobalTheory.Reg.Covers P ∧ ∀ j, evR Xo c f (P j).yg ∈ Algebra.adjoin c.F ((P j).gens : Set (P j).Ω) := by
  first | exact @GlobalTheory.CuspReg.exists_cover_noPole | exact GlobalTheory.CuspReg.exists_cover_noPole | (intros; apply GlobalTheory.CuspReg.exists_cover_noPole <;> assumption)
