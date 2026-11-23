import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConstCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoFrameLoc

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def eP (k r : ℕ) (z' ν v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  SSn.prWv k r z' v - herm (Hpk k r) (SSn.prWv k r z' v) ν • ν

theorem eP_add (z' ν x y : Fin (2 * r + k + 1) → ℂ) : eP k r z' ν (x + y) = eP k r z' ν x + eP k r z' ν y := by
  unfold eP
  rw [PRhoCut.FL.prWv_add, DU.hadd_l, add_smul]
  abel

theorem eP_smul (z' ν : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    eP k r z' ν (c • x) = c • eP k r z' ν x := by
  unfold eP
  rw [PRhoCut.FL.prWv_smul, DU.hsmul_l, smul_sub, smul_smul]

def ioLin (k r : ℕ) (μ : B.Mat k r) (z' ν : Fin (2 * r + k + 1) → ℂ) :
    (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) where
  toFun v := μ *ᵥ eP k r z' ν v
  map_add' x y := by rw [eP_add, Matrix.mulVec_add]
  map_smul' c x := by rw [eP_smul, Matrix.mulVec_smul]; rfl

theorem ioMulVec (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ)
    (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.io0 k r z z' μsec ζ *ᵥ v = NF.muZ k r μsec ζ *ᵥ (SSn.prWv k r z' v -
      herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ) := by
  have e : SSn.io0 k r z z' μsec ζ =
      LinearMap.toMatrix' (ioLin k r (NF.muZ k r μsec ζ) z' (SSn.nu0' k r z z' μsec ζ)) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [e, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
