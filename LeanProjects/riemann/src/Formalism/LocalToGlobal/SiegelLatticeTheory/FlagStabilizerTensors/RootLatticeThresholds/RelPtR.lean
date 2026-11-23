import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOfR

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open Matrix

namespace Formalism.L2.SG.Pf.RelPtR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem rv_crd_fvec (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    rv X.B.I v (X.crd ((X.Fu u).fvec a)) = Formalism.L2.SG.RealObj.frm X u 1 v a := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · rw [FlagG.fvec, Fin.snoc_last, X.flagZVector u, Fin.snoc_last]
    rfl
  · rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u, Fin.snoc_castSucc]
    rfl

theorem zhatP_eq (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) *
        Formalism.L2.SG.RealObj.ZX X u u' 1 (Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ) a b := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ)
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) a b =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a)
        (uMat ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ)) *ᵥ
          (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) b)) := by
    unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm Formalism.L2.SG.Pf.JointAmplitudePoints.gamP Formalism.L2.SG.RealObj.trG hJ
    rw [← hH, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT]
    congr 1
    simp only [Matrix.mulVec_mulVec]
    congr 1
    rw [show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ *
        (C.Qi τ * uMat ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ)) * C.Q τ) =
      (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) *
        uMat ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ)) * C.Q τ by
        simp only [Matrix.mul_assoc], hQQi]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hA, Formalism.L2.SG.Pf.LTL.Q_fvec C u τ a, Formalism.L2.SG.Pf.LTL.Q_fvec C u' τ b, Matrix.mulVec_smul,
    Formalism.L2.SG.Pf.LTL.hJ_smul_real, rv_crd_fvec, rv_crd_fvec]
  rfl

theorem alf_eq (D : D7) (a : Fin (D.R.rS + 1)) : Formalism.MainNotions.BesselShellMomentBounds.alf D a = rhoF D a := by
  unfold Formalism.MainNotions.BesselShellMomentBounds.alf rhoF
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  ring

theorem ptMat_ptLoc (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) (a b : Fin (D.R.rS + 1)) :
    ptMat (ptLoc D τ w) a b = ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (ptMat w a b) := by
  have h := Formalism.MainNotions.BesselShellMomentBounds.ptEntry_loc D τ w.1 0 a b
  simp only [Nat.zero_add] at h
  change ptEntry (locBlocksFrom D (rhoReal D) τ 0 w.1) a b = _
  rw [h, alf_eq D a, alf_eq D b]
  rfl

variable (u u' : D.what₂.Word)

theorem zhatO_gamP (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g)
    (τ : D.what₂.Tau) :
    ZhatO D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) =
      ptMat (ptLoc D τ w) := by
  have hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w (Formalism.L2.SG.RealObj.gamW X u u' w) := by
    unfold Formalism.L2.SG.RealObj.gamW
    rw [dif_pos hw]
    exact hw.choose_spec
  ext a b
  have h1 := congrFun (congrFun (hrep (vOf X τ)) a) b
  unfold Formalism.L2.SG.RealObj.ZhatO Formalism.L2.SG.RealObj.ptC at h1
  simp only [Matrix.map_apply] at h1
  rw [X.φ_eq, X.ιE.apply_symm_apply, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h1
  unfold ZhatO
  rw [zhatP_eq C u u' w τ a b, ptMat_ptLoc τ w a b, ← h1]
  ring

theorem normSq_dmin (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) (l : Fin (D.R.rS + 2)) :
    Complex.normSq (Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' g l) =
      Complex.normSq (((ZhatO D.R.k D.R.rS z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
        (Fin.castLE (Nat.le_of_lt_succ l.isLt))).det) := by
  unfold Formalism.QuantumDeterminants.Dmin
  have hM : (ZhatO D.R.k D.R.rS z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
      (Fin.castLE (Nat.le_of_lt_succ l.isLt)) =
      (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
        (Fin.castLE (Nat.le_of_lt_succ l.isLt)) *
      Matrix.diagonal (fun b : Fin l.val => (-1 : ℂ) ^ (D.R.rS - (Fin.castLE (Nat.le_of_lt_succ l.isLt) b).val)) := by
    ext i j
    simp [ZhatO, Matrix.mul_diagonal, mul_comm]
  rw [hM, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod]
  simp [Complex.normSq_neg]

theorem gf_gamP (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g)
    (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) =
      Gpt (((D.mem u).A.T : ℕ) : ℝ) (((D.mem u').A.T : ℕ) : ℝ) (ptLoc D τ w) := by
  unfold Formalism.QuantumDeterminants.Gf Gpt
  rw [normSq_dmin, normSq_dmin, zhatO_gamP C u u' w hw τ, Formalism.L2.SG.Pf.LTL.tz_zB C u τ,
    Formalism.L2.SG.Pf.LTL.tz_zB C u' τ]
  rfl

theorem relPtExPR_holds : Formalism.L2.SG.Pf.BDatR.RelPtExPR u u' C := by
  intro w hb hw τ
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _, ?_, ?_⟩
  · refine ⟨(1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ),
      fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => by subst h; exact Matrix.one_apply_eq i⟩,
      fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h).symm, fun h => by subst h; exact Matrix.one_apply_eq i⟩, ?_⟩
    rw [Matrix.one_mul, Matrix.mul_one, zhatO_gamP C u u' w hw τ]
  · rw [gf_gamP C u u' w hw τ]
    exact (hb.2 τ).ne'

end Formalism.L2.SG.Pf.RelPtR
