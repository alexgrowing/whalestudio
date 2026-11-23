import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumFinitePlacesLeSumOverPrimes
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algDefStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.QBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_finitePlaces_le_sum_over_primes : ∀ (K : Type) [Field K] [NumberField K] (φ : ℕ → ℝ) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p, 0 ≤ φ p) → ∀ ν : HeightOneSpectrum (𝓞 K) → ℝ, (∀ la, 0 ≤ ν la) → (∀ la, ν la ≤ (ramOverZ la : ℝ) * φ (resCharOf la)) → (∀ la, resCharOf la ∉ S → ν la = 0) → (Function.support ν).Finite ∧ (∑ᶠ la, |ν la| * (Real.log (Ideal.absNorm la.asIdeal) / Module.finrank ℚ K)) ≤ ∑ p ∈ S, φ p * Real.log p := by
  first | exact @GlobalTheory.PlaceSum.finsum_le_sum_primes | exact GlobalTheory.PlaceSum.finsum_le_sum_primes | (intros; apply GlobalTheory.PlaceSum.finsum_le_sum_primes <;> assumption)
