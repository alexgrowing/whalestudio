import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgIndepOfSameAdjoin
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alg_indep_of_same_adjoin : ∀ (K L J : Type) [Field K] [Field L] [Algebra K L] [Finite J] (x y : J → L), AlgebraicIndependent K x → IntermediateField.adjoin K (Set.range x) = IntermediateField.adjoin K (Set.range y) → AlgebraicIndependent K y := by
  first | exact @GlobalTheory.CompanionTheory.FieldGen.algebraicIndependent_of_adjoin_eq | exact GlobalTheory.CompanionTheory.FieldGen.algebraicIndependent_of_adjoin_eq | (intros; apply GlobalTheory.CompanionTheory.FieldGen.algebraicIndependent_of_adjoin_eq <;> assumption)
