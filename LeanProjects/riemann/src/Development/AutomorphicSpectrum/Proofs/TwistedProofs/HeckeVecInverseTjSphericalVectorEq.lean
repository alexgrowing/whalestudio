import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.LinActOneOneApply
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ACo
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsSmulOfMapResidueEqZero

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CompanionTheory.Ipf.Val GlobalTheory.CompanionTheory.Ipf.Val.SphM
open Formalism.UG (Tj Ov qV IsUnifV Hecke conv dosetInd diagJ)
open GlobalTheory.LFun (KGL heckeVec)
open GlobalTheory.SplitHecke (IsInt IntM GInt Hk Reps yw nKer)

namespace GlobalTheory.CompanionTheory.Ipf.Val.SphM.TjInv

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def tJ (c j : ℕ) {ϖ : Cv v} (h : ϖ ≠ 0) : GL (Fin c) (Cv v) where
  val := diagJ c ϖ j
  inv := Matrix.diagonal fun i => if (i : ℕ) < j then ϖ⁻¹ else 1
  val_inv := by
    rw [diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [h]
  inv_val := by
    rw [diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [h]

def sc (c : ℕ) {ϖ : Cv v} (h : ϖ ≠ 0) : GL (Fin c) (Cv v) where
  val := ϖ • 1
  inv := ϖ⁻¹ • 1
  val_inv := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h, Matrix.one_mul, one_smul]
  inv_val := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h, Matrix.one_mul, one_smul]

section Main

variable {c j : ℕ} {ϖ : Cv v}

variable {R : Finset (GL (Fin c) (Cv v))}

end Main

end GlobalTheory.CompanionTheory.Ipf.Val.SphM.TjInv

end
