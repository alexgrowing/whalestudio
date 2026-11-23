import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastUnitLocusOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_unit_locus_open : ∀ (S' : Scheme.{0}) (d : ℕ), ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsUnit ((d : ℕ) : Γ(V.toScheme, ⊤))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S'), IsUnit ((d : ℕ) : Γ(T, ⊤)) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.UnitLocus.natCast_unit_locus) | (exact GlobalTheory.UnitLocus.natCast_unit_locus) | (intros; apply GlobalTheory.UnitLocus.natCast_unit_locus  <;> assumption)
