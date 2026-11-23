import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.GENSL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymplecticFourierGaussian
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurePreservingMixedSpaceReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AddCharConductorInv
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar restrictedTensor2 awayBox awayIntegral vecAt)
open GroundTheory.Automorphic.GJMatrix (localFourierPi localMeasurePi)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3.R (G2 Jd md KA LInv pri dia2 pt)
open Matrix
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate SchwartzMap Classical

noncomputable section

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.CPois

open NumberField.mixedEmbedding

def rc (m : mixedSpace ℚ) : ℝ := m.1 ⟨Ad3.GP.wR, Ad3.GP.wR_isReal⟩

theorem rc_ext {m m' : mixedSpace ℚ} (h : rc m = rc m') : m = m' := by
  haveI := GlobalTheory.CompanionTheory.RealAdele.isEmpty_isComplex
  refine Prod.ext (funext fun w => ?_) (funext fun w => isEmptyElim w)
  have e : w = ⟨Ad3.GP.wR, Ad3.GP.wR_isReal⟩ := Subtype.ext (Subsingleton.elim _ _)
  rw [e]
  exact h

def rcE : mixedSpace ℚ ≃L[ℝ] ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := rc
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun t => (fun _ => t, fun _ => 0)
      left_inv := fun m => rc_ext rfl
      right_inv := fun _ => rfl }

def rc2 : (Fin 2 → mixedSpace ℚ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight fun _ => rcE

def negM (M : Matrix (Fin 2) (Fin 2) ℚ) (hd : M.det ≠ 0) : (Fin 2 → ℚ) ≃ (Fin 2 → ℚ) where
  toFun z := -(M *ᵥ z)
  invFun y := -(M⁻¹ *ᵥ y)
  left_inv z := by
    change -(M⁻¹ *ᵥ -(M *ᵥ z)) = z
    rw [Matrix.mulVec_neg, neg_neg, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd), Matrix.one_mulVec]
  right_inv z := by
    change -(M *ᵥ -(M⁻¹ *ᵥ z)) = z
    rw [Matrix.mulVec_neg, neg_neg, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.one_mulVec]

end GlobalTheory.CompanionTheory.CPois
