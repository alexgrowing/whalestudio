import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerKilledOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelKilledOverOpen_of_local : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (W : S'.Opens), (∀ p ∈ W, ∃ V : S'.Opens, p ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V) → GlobalTheory.KerKilledLocus.KerKilledOn d G P W := by
  first | (exact @GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (exact GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (intros; apply GlobalTheory.KerKilledLocal.kerKilledOn_of_local <;> assumption)
