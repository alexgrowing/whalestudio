import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtOfDivisorRelation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_at_of_divisor_relation : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (ι : Type) [Fintype ι] (DM : Y.Dv) (D : ι → Y.Dv) (q : ℕ) (b : ι → ℤ) (x : Y.X) (fM : Y.Fn) (f : ι → Y.Fn), q • DM = ∑ i, b i • D i → DM.GeneratesAt x fM → (∀ i, (D i).GeneratesAt x (f i)) → UnitAt x (fM ^ q / ∏ i, f i ^ b i) := by
  first | exact @GlobalTheory.CombUnit.unitAt_quot_of_relation | exact GlobalTheory.CombUnit.unitAt_quot_of_relation | (intros; apply GlobalTheory.CombUnit.unitAt_quot_of_relation <;> assumption)
