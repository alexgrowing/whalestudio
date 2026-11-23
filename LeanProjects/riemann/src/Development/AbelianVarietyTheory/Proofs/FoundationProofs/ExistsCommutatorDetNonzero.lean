import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem commutator_H0_has_no_eigenvalue_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W →
    ∃ φ ∈ ⁅H0g W, H0g W⁆, (mat W φ - 1).det ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.CommutingExistence.main
  | exact _root_.GlobalTheory.CommutingExistence.main
  | (apply _root_.GlobalTheory.CommutingExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommutingExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommutingExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommutingExistence.main ..)

end GlobalTheory.Ord2
