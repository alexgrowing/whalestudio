import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStepCharactersOfColength
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagStep_characters_of_colength : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ (f : Lt1 Dw) (xs : NNReal) (r : ℝ), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult f.1)) j => X.ι (Ch.uvecT ⟨f.1, i⟩ j)) xs → (X.v (p : X.C) : ℝ) ^ r ≤ xs → HasChars (fgl Ch X) (frame Ch X f) (r : EReal) ∧ ∀ k : ℕ, nuFac p y f k ≤ ((k * r : ℝ) : EReal) := by
  first | exact @GlobalTheory.RefSum.hasChars_frame_of_hasAF | exact GlobalTheory.RefSum.hasChars_frame_of_hasAF | (intros; apply GlobalTheory.RefSum.hasChars_frame_of_hasAF <;> assumption)
