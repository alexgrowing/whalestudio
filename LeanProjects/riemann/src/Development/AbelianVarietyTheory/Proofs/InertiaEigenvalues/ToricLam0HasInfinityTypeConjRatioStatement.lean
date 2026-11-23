import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatio
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_kap_and_lam0_hasInf : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → (∀ g, 1 ≤ Z.kap j a s g) ∧ GlobalTheory.CMVal.HasInf (Z.lam0 l j a) (phi D.host) (fun g => (Z.kap j a s g : ℤ) + s) := by
  first | exact @GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio | exact GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio | (intros; apply GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio <;> assumption)
