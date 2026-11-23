import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairTwoStepExchange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_two_step_exchange : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (E E' : B.X.Modules) (φ : B.GenIso E E') (r m : ℕ) (hm : m + 2 ≤ r) (P P' : GlobalTheory.Vert.Model.FlagPair φ r), P.fl.SameStep P'.fl ⟨m, by omega⟩ → P.fl.SameStep P'.fl ⟨m + 2, by omega⟩ → P.fl'.SameStep P'.fl' ⟨m, by omega⟩ → P.fl'.SameStep P'.fl' ⟨m + 2, by omega⟩ → ∃ (W W' : B.X.Modules) (ψ : B.GenIso W W') (R R' : GlobalTheory.Vert.Model.FlagPair ψ 2), ((R.toFPair p).x 0 = (P.toFPair p).x ⟨m, by omega⟩ ∧ (R.toFPair p).x' 0 = (P.toFPair p).x' ⟨m, by omega⟩ ∧ (R.toFPair p).Dv 0 = (P.toFPair p).Dv ⟨m, by omega⟩ ∧ (R.toFPair p).x 1 = (P.toFPair p).x ⟨m + 1, by omega⟩ ∧ (R.toFPair p).x' 1 = (P.toFPair p).x' ⟨m + 1, by omega⟩ ∧ (R.toFPair p).Dv 1 = (P.toFPair p).Dv ⟨m + 1, by omega⟩) ∧ ((R'.toFPair p).x 0 = (P'.toFPair p).x ⟨m, by omega⟩ ∧ (R'.toFPair p).x' 0 = (P'.toFPair p).x' ⟨m, by omega⟩ ∧ (R'.toFPair p).Dv 0 = (P'.toFPair p).Dv ⟨m, by omega⟩ ∧ (R'.toFPair p).x 1 = (P'.toFPair p).x ⟨m + 1, by omega⟩ ∧ (R'.toFPair p).x' 1 = (P'.toFPair p).x' ⟨m + 1, by omega⟩ ∧ (R'.toFPair p).Dv 1 = (P'.toFPair p).Dv ⟨m + 1, by omega⟩) := by
  first | exact @GlobalTheory.Vert.Model.FlagPair.exists_rankTwo_subquotient | exact GlobalTheory.Vert.Model.FlagPair.exists_rankTwo_subquotient | (intros; apply GlobalTheory.Vert.Model.FlagPair.exists_rankTwo_subquotient <;> assumption)
