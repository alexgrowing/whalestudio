import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section

namespace GlobalTheory.SlocTie

def rmulE {k r : ℕ} (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hab : a * b = 1) (hba : b * a = 1) :
    Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun x := Matrix.of.symm (Matrix.of x * a)
  invFun x := Matrix.of.symm (Matrix.of x * b)
  left_inv x := by
    show Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of x * a)) * b) = x
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, hab, Matrix.mul_one]; rfl
  right_inv x := by
    show Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of x * b)) * a) = x
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, hba, Matrix.mul_one]; rfl
  measurable_toFun := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun x : Formalism.QuantumDeterminants.Mt k r => ∑ l, x i l * _
    fun_prop
  measurable_invFun := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun x : Formalism.QuantumDeterminants.Mt k r => ∑ l, x i l * _
    fun_prop

theorem quot_rmul {k r : ℕ} (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hab : a * b = 1)
    (hba : b * a = 1) {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : μG.map (rmulE a b hab hba) = μG)
    (hq : IsQuotMeas μG μS ν) : IsQuotMeas μG μS (ν.map (rmulE a b hab hba)) := by
  intro f hf
  set R := rmulE a b hab hba
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, f x ∂(μG.map R) := by rw [hG]
    _ = ∫⁻ x, f (R x) ∂μG := MeasureTheory.lintegral_map_equiv _ R
    _ = ∫⁻ x, (∫⁻ s, f (R (fun i j => (Matrix.of s * Matrix.of x) i j)) ∂μS) ∂ν := hq _ (hf.comp R.measurable)
    _ = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (R x)) i j) ∂μS) ∂ν := by
        refine lintegral_congr fun x => lintegral_congr fun s => ?_
        congr 1
        show Matrix.of.symm (Matrix.of (fun i j => (Matrix.of s * Matrix.of x) i j) * a) =
          fun i j => (Matrix.of s * Matrix.of (Matrix.of.symm (Matrix.of x * a))) i j
        rw [Equiv.apply_symm_apply]
        funext i j
        show (Matrix.of s * Matrix.of x * a) i j = (Matrix.of s * (Matrix.of x * a)) i j
        rw [Matrix.mul_assoc]
    _ = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂(ν.map R) :=
        (MeasureTheory.lintegral_map_equiv (fun x => ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) R).symm

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def yInv (C : Choice X θ) (τ : D.what₂.Tau) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS

theorem y_inv (C : Choice X θ) (τ : D.what₂.Tau) : C.y τ * yInv C τ = 1 ∧ yInv C τ * C.y τ = 1 := by
  obtain ⟨-, hi⟩ := Formalism.MainNotions.S.Inh.unitary_group_inv_mem (C.y τ) (C.y_mem τ)
  exact ⟨(Matrix.mul_eq_one_comm_of_card_eq (Fin _) (Fin _) ℂ rfl).mp hi, hi⟩

def Ry (C : Choice X θ) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS ≃ᵐ Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  rmulE (C.y τ) (yInv C τ) (y_inv C τ).1 (y_inv C τ).2

theorem muGB_rinv (C : Choice X θ) (τ : D.what₂.Tau) :
    (muGB X (C.Q τ) (C.Qi τ) τ).map (Ry C τ) = muGB X (C.Q τ) (C.Qi τ) τ := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hy' : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hJ : (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    calc (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ)
        = (C.Qi τ)ᴴ * ((C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.y τ) * C.Qi τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hy', Formalism.L2.SG.Pf.Choice.qiHqi _ h2 hg]
  set γy := Formalism.L2.SG.Pf.GoodS.toUJn (C.Q τ * C.y τ * C.Qi τ) hJ
  haveI : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  have he := eT_emb C τ (vOf X τ)
  have hcomm : (Ry C τ) ∘ eT C τ (vOf X τ) = eT C τ (vOf X τ) ∘ (fun γ => γ * γy) := by
    funext γ
    show Matrix.of.symm (Matrix.of (Matrix.of.symm (C.Qi τ * uMat γ * C.Q τ)) * C.y τ) =
      Matrix.of.symm (C.Qi τ * uMat (γ * γy) * C.Q τ)
    rw [Equiv.apply_symm_apply, show uMat (γ * γy) = uMat γ * uMat γy from rfl,
      show uMat γy = C.Q τ * C.y τ * C.Qi τ from rfl]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one]
  show ((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (eT C τ (vOf X τ))).map (Ry C τ) =
    (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (eT C τ (vOf X τ))
  rw [Measure.map_map (Ry C τ).measurable he.measurable, hcomm,
    ← Measure.map_map he.measurable (measurable_mul_const γy), map_mul_right_eq_self]

def shiftC (C : Choice X θ) : Choice X θ :=
  { C with
    nuS := fun u τ => (C.nuS u τ).map (Ry C τ)
    nuS_q := fun u τ => quot_rmul _ _ _ _ (muGB_rinv C τ) (C.nuS_q u τ) }

theorem loc_main (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word)
    (τ : D.what₂.Tau) :
    ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) ∧
      ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
        l2SG (C.nuS u τ) (phiOf hB u τ) := by
  obtain ⟨β, hβm, hβ1⟩ := bruhat_mulMap C u τ
  refine ⟨β, hβm, hβ1, ?_⟩
  have hid := loc_id (shiftC C) u τ hβm hβ1
  rw [hid]
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  have hconc := Formalism.L2.SG.Pf.GoodS.nu_conc hz hT (Formalism.L2.SG.Pf.haarTr C τ) (Formalism.L2.SG.Pf.LocF.muS_haar C u τ)
    (C.nuS_q u τ)
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  show ∫⁻ x, (‖wT C u τ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂((C.nuS u τ).map (Ry C τ)) =
    ∫⁻ x, (‖phiOf hB u τ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂(C.nuS u τ)
  rw [MeasureTheory.lintegral_map_equiv]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [Formalism.L2.SG.Pf.GoodS.phi_eq C hB u τ _ hx]
  rfl

end GlobalTheory.SlocTie
