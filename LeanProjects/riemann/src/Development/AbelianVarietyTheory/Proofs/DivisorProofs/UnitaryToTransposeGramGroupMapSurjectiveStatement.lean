import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToTransposeGramGroupMapSurjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToTransposeGramGroupMap_surjective : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • Matrix.reindex e e X.gramᵀ), Function.Surjective (GlobalTheory.SquareAgree.kapX X e hJ) := by
  first | exact @GlobalTheory.SquareAgree.kapX_surjective | exact GlobalTheory.SquareAgree.kapX_surjective | (intros; apply GlobalTheory.SquareAgree.kapX_surjective <;> assumption)
