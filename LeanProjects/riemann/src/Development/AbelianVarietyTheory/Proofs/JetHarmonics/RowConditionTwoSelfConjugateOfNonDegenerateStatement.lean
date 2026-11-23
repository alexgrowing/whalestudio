import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowConditionTwoSelfConjugateOfNonDegenerate
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankMaximal_rawSelf_of_ndg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), NDG Y → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc := by
  first | exact @GlobalTheory.RowAtSelf.rowCondition_two_selfConjugate_of_nonDegenerate | exact GlobalTheory.RowAtSelf.rowCondition_two_selfConjugate_of_nonDegenerate | (intros; apply GlobalTheory.RowAtSelf.rowCondition_two_selfConjugate_of_nonDegenerate <;> assumption)
