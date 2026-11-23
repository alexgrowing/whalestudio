import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledUniformization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rescaled_uniformization : ∀ (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g) (lam : Fin g → ℂ),
    (∀ j, lam j ≠ 0) → ∃ u' : HolUnif A Lb g, (∀ w, u'.ex w = u.ex (fun j ↦ lam j * w j)) ∧
      (∀ (d : Fin g → ℝ) χ, u.IsAH (Matrix.diagonal fun j ↦ (d j : ℂ)) χ →
        ∃ χ', u'.IsAH (Matrix.diagonal fun j ↦ ((d j * ‖lam j‖ ^ 2 : ℝ) : ℂ)) χ') ∧
      (∀ W v, u'.IsDiff W v ↔ u.IsDiff (fun j ↦ lam j * W j) v) := by
  first | exact @GlobalTheory.holUnif_rescale | exact GlobalTheory.holUnif_rescale | (intros; apply GlobalTheory.holUnif_rescale <;> assumption)
