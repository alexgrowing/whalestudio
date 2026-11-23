import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRationalPointTestSupportDoubleCosetsFinit
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularRationalPoint_testSupport_doubleCosets_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) (finPt γ) : Set (finU E n)) (globLev S K' : Set (finU E n)) | globFn S f ((Quotient.out q)⁻¹ * finPt γ * (MonoidHom.id (finU E n)) (Quotient.out q)) ≠ 0}.Finite := by
  first | exact @GlobalTheory.BCT.ClsSupp.finite_supp | exact GlobalTheory.BCT.ClsSupp.finite_supp | (intros; apply GlobalTheory.BCT.ClsSupp.finite_supp <;> assumption)
