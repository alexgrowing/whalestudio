import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_act_eq_inner_act_adjZ_of_hasDerivAt : ∀ (p q : ℕ) (T : GrpData p q) (πU : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) := by
  first | exact @GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint | exact GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint | (intros; apply GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint <;> assumption)
