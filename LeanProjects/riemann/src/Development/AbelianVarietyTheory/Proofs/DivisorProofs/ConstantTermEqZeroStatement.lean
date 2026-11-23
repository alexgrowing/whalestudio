import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_of_isCuspForm' : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ → GroundTheory.Automorphic.AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 := by
  first | exact @GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero | exact GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero | (intros; apply GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero <;> assumption)
