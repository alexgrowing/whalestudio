import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfDataAdelicMetricPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlagOfHalfDataStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag

theorem GlobalTheory.WholeFlag.halfFlag_whole : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core →
    ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → ∀ c : O.s.Comp,
    HalfFlag (fun k : Fin (D.R.f * O.N) => adlOf (O.Φ.C c) (O.met.hm c)
      (wholeSym (Function.update (ArIn.ind Sx) p true) (some R)
        (Sum.inl k : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))) p :=
  fun h2 hH hRA hSW D O hO Sx R hR p hp c =>
    GlobalTheory.T.halfFlag_of_halfData _ p hp (GlobalTheory.T.half_data_adelic_metric_prime h2 hH hRA hSW D O hO Sx R hR p hp c)
