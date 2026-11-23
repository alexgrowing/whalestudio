import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsGoodSplitPrimeCmField
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_split_prime_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (m : ℕ), 0 < m → ∃ (q : ℕ) (P : Ideal (𝓞 E)), GoodPrime m q P := by
  first | exact @GlobalTheory.SW.SplitPrime.exists_goodPrime | exact GlobalTheory.SW.SplitPrime.exists_goodPrime | (intros; apply GlobalTheory.SW.SplitPrime.exists_goodPrime <;> assumption)
