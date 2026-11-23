import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FreeAndRankBoundIntegers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_and_rank_bound_integers : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (NumberField.RingOfIntegers E) X]
    [Module.Finite (NumberField.RingOfIntegers E) X] [Module.Projective (NumberField.RingOfIntegers E) X],
    Module.Free ℤ X ∧ Module.finrank ℤ X ≤ Module.finrank ℚ E * Module.finrank (NumberField.RingOfIntegers E) X := by
  first | exact @GlobalTheory.ZRank.free_int_and_finrank_le | exact GlobalTheory.ZRank.free_int_and_finrank_le | (intros; apply GlobalTheory.ZRank.free_int_and_finrank_le <;> assumption)
