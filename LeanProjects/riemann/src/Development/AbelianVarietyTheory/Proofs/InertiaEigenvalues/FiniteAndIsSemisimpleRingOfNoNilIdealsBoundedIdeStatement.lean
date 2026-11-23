import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAndIsSemisimpleRingOfNoNilIdealsBoundedIde
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents : ∀ (k R : Type) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] (d : ℕ), (∀ x : R, IsIntegral k x) → (∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) → (∀ (m : ℕ) (e : Fin m → R), OrthogonalIdempotents e → (∀ i, e i ≠ 0) → m ≤ d) → Module.Finite k R ∧ IsSemisimpleRing R := by
  first | exact @GlobalTheory.AlgRing.finite_and_isSemisimpleRing | exact GlobalTheory.AlgRing.finite_and_isSemisimpleRing | (intros; apply GlobalTheory.AlgRing.finite_and_isSemisimpleRing <;> assumption)
