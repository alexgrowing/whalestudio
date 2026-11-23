import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecRelAmplePowDivNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_sec_relAmplePow_div_ne_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left), IsProper A.hom → Nonempty A.left → L.IsLB → M.IsLB → Out.RelAmple A M → ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ ∃ j, s.f j ≠ 0 := by
  first | exact @GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero | exact GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero | (intros; apply GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero <;> assumption)
