import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
theorem _root_.GlobalTheory.T.finite_twisted_classes_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (Q : (w.adicCompletion E)[X]), Q.Separable → {c : TwCl (thL n w) | (nrmL n w c.rep).val.charpoly = Q}.Finite ∧ {c : TwCl (MonoidHom.id (UL n w)) | c.rep.1.val.charpoly = Q}.Finite := by
  first | exact @GlobalTheory.BCT.ClsFin.classes_finite | (intros; apply GlobalTheory.BCT.ClsFin.classes_finite <;> assumption)
