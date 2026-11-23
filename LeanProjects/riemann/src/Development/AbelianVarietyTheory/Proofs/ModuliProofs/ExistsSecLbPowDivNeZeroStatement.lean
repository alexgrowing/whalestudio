import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecLbPowDivNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_nonzero_sec_lbPow_div : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left), N.IsLB → ∃ (n : ℕ) (s : (LB.div (lbPow P.L n) N).Sec), ∃ j, s.f j ≠ 0 := by
  first | exact @GlobalTheory.exists_sec_lbPow_div_ne_zero | exact GlobalTheory.exists_sec_lbPow_div_ne_zero | (intros; apply GlobalTheory.exists_sec_lbPow_div_ne_zero <;> assumption)
