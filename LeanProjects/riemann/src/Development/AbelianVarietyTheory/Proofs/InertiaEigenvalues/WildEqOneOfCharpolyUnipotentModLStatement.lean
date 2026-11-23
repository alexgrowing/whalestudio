import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wild_eq_one_of_charpoly_unipotent_mod_l : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g l n : ℕ) [Fact g.Prime] [Fact l.Prime], l ≠ g → A.valuation (g : Ω) < 1 → ∀ (K : Type) [Field K] [CharP K l] (rb : G E Ω →* GL (Fin n) K), IsOpen (rb.ker : Set (G E Ω)) → ∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → ((rb s : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n → rb s = 1 := by
  first | exact @GlobalTheory.WildKill.eq_one_of_wild_of_unipotent | exact GlobalTheory.WildKill.eq_one_of_wild_of_unipotent | (intros; apply GlobalTheory.WildKill.eq_one_of_wild_of_unipotent <;> assumption)
