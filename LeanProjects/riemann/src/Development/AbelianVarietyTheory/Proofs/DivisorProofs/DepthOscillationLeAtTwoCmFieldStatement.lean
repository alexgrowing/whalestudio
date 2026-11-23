import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmField
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AutomorphicArithmetic.CMTraceForms.Places
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_oscillation_le_at_two_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime] (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H F vd → OscLe Xo c p cx (F * m * (1 + vd / 2) * Mb + Sm) := by
  first | exact @GlobalTheory.RefSum.oscLe_two | exact GlobalTheory.RefSum.oscLe_two | (intros; apply GlobalTheory.RefSum.oscLe_two <;> assumption)
