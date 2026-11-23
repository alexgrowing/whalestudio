import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
noncomputable section

open Module

namespace GlobalTheory.Pst.UnitLetter

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (L : FinExt l)

def toA : ((Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) ≃ₗ[ℚ_[l]] Bst P ⊗[ℚ_[l]] ↥L.1 :=
  (TensorProduct.congr (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1) (LinearEquiv.refl ℚ_[l] (Bst P))).trans
    (TensorProduct.comm ℚ_[l] ↥L.1 (Bst P))

@[simp] theorem toA_tmul (v : Fin 1 → ↥L.1) (b : Bst P) : toA P L (v ⊗ₜ b) = b ⊗ₜ v 0 := rfl

variable {P L}

theorem toA_mulB (y' y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' y) = toA P L y' * toA P L y := by
  induction y' using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [GlobalTheory.Pst.TwistLetters.mulB_tmul, toA_tmul, toA_tmul, toA_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      simp
    | add x x' hx hx' => simp only [map_add, mul_add, hx, hx']
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, add_mul, hy, hy']

theorem toA_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (mulV P ↥L.1 (Fin 1 → ↥L.1) c y) = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c • toA P L y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, toA_tmul, toA_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x x' hx hx' => simp only [map_add, smul_add, hx, hx']

theorem toA_stRep {K : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)
    (hm : ∀ g v, ρm g v = χ g • v) (g : ↥(GK K)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (stRep P ρm g y) =
      Algebra.TensorProduct.map (actSt P (g : GQ l)) (AlgHom.id ℚ_[l] ↥L.1) (toA P L y) *
        ((1 : Bst P) ⊗ₜ[ℚ_[l]] χ g) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [stRep_tmul, toA_tmul, toA_tmul, hm, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp [mul_comm]
  | add x x' hx hx' => simp only [map_add, add_mul, hx, hx']

end GlobalTheory.Pst.UnitLetter
