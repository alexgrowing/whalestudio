import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantPerturbationBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_perturbation_bound : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] (J : Type) (k : ℕ) (P P' : J → Fin k → C) (N : ℝ), 0 < N → (∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ ≤ N) → (∃ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ = N) → (∀ cf : Fin k → C, (∀ j, ‖∑ l, cf l * P j l‖ ≤ 1) → ∀ j, ‖∑ l, cf l * (P j l - P' j l)‖ < 1) → ∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det - (Matrix.of fun r l => P' (σ r) l).det‖ < N := by
  first | exact @GlobalTheory.det_sub_lt_of_close_on_unitBall | exact GlobalTheory.det_sub_lt_of_close_on_unitBall | (intros; apply GlobalTheory.det_sub_lt_of_close_on_unitBall <;> assumption)
