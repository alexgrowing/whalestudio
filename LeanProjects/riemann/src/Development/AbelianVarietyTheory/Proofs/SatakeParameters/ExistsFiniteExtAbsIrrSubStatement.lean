import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteExtAbsIrrSub
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
open Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr : ∀ {K Γ ι : Type} [Field K] [Group Γ] [Finite ι] {a : ℕ} (ρ : ι → (Γ →* GL (Fin a) K)), (∀ j, IsSSRep (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j))) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), ∀ j W, IsIrrSub (mapRep (algebraMap K K') (ρ j)) W → AbsIrrSub (mapRep (algebraMap K K') (ρ j)) W := by
  first | exact @GlobalTheory.SplitField.exists_finite_ext_absIrrSub | exact GlobalTheory.SplitField.exists_finite_ext_absIrrSub | (intros; apply GlobalTheory.SplitField.exists_finite_ext_absIrrSub <;> assumption)
