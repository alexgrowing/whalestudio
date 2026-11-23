import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam0_isUnitary_and_trivOnF : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m), (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | exact GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | (intros; apply GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield <;> assumption)
