import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntLoc

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntLoc

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem cStd_ne : Formalism.QuantumDeterminants.cStd ≠ 0 := by
  simp [Formalism.QuantumDeterminants.cStd]

theorem muNc_haar (hθ : 0 < θ) :
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) ((muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) :=
  haarN_tor (Formalism.L2.SG.Pf.muT_ne D)
    (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (Formalism.L2.SG.Pf.Choice.kapN_ne_zero D hθ) ENNReal.ofReal_ne_top)

theorem hty_c (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    IsHCTypeW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ) := by
  have h := Formalism.L2.SG.Pf.Choice.colsTypeTr_of X (Formalism.L2.SG.Pf.cfS_ne D) (transpC' C τ) u
  rw [zc_eq] at h
  have hp : X.pl (vOf X τ) = τ := by
    first
    | simp [vOf]
    | (unfold vOf; simp)
    | rfl
  rw [hp] at h
  exact h

theorem zT (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ) ∧ 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
  refine ⟨(Formalism.L2.SG.Pf.zTr C u τ).1, ?_⟩
  rw [(Formalism.L2.SG.Pf.zTr C u τ).2]
  exact Formalism.L2.SG.Pf.Choice.Tr_pos D u

def Dc (C : Choice X θ) (hθ : 0 < θ) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.FourierDecayAlt.B.RealPlaceData D.R.k D.R.rS (X.Vloc u (vOf X τ)) (X.Vloc u' (vOf X τ)) where
  z := zB X (C.Qi τ) u τ
  z' := zB X (C.Qi τ) u' τ
  π := piB X (Qcs C τ) (Qics C τ) u τ
  π' := piB X (Qcs C τ) (Qics C τ) u' τ
  μG := muGB X (Qcs C τ) (Qics C τ) τ
  μW := C.muW u τ
  μN := (muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))
  μW' := C.muW u' τ
  μsec := (Formalism.L2.SG.Pf.BaseOf.sec_exists (Formalism.L2.SG.Pf.BaseOf.k_pos D) _ _ (zT C u τ).2 (zT C u' τ).2
    (let ⟨g, hg, _⟩ := hty_c C u τ; ⟨g, hg⟩) (let ⟨g, hg, _⟩ := hty_c C u' τ; ⟨g, hg⟩)).choose
  χ := Formalism.FourierDecayAlt.P.character_exists_alt.choose
  k_pos := Formalism.L2.SG.Pf.BaseOf.k_pos D
  z_mem := (zT C u τ).1
  z'_mem := (zT C u' τ).1
  T_pos := (zT C u τ).2
  T'_pos := (zT C u' τ).2
  π_rep := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u τ).1 (zT C u τ).2 (hty_c C u τ)).1
  π'_rep := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (hty_c C u' τ)).1
  π_unitary := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u τ).1 (zT C u τ).2 (hty_c C u τ)).2.1
  π'_unitary := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (hty_c C u' τ)).2.1
  π_cont := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u τ).1 (zT C u τ).2 (hty_c C u τ)).2.2
  π'_cont := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (hty_c C u' τ)).2.2
  haarG := Formalism.L2.SG.Pf.BaseOf.haarG_B (n_eq' X) (X.B.I.ε (vOf X τ)) (transpC' C τ).2.1 (transpC' C τ).2.2.1
  haarW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zT C u τ).1 (zT C u τ).2 (C.muW_haar u τ)
  haarN := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (muNc_haar hθ)
  haarW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (C.muW_haar u' τ)
  sec := (Formalism.L2.SG.Pf.BaseOf.sec_exists (Formalism.L2.SG.Pf.BaseOf.k_pos D) _ _ (zT C u τ).2 (zT C u' τ).2
    (let ⟨g, hg, _⟩ := hty_c C u τ; ⟨g, hg⟩) (let ⟨g, hg, _⟩ := hty_c C u' τ; ⟨g, hg⟩)).choose_spec
  χ_smooth := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.1
  χ_supp := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.1
  χ_int := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.2

theorem sideC (C : Choice X θ) (hθ : 0 < θ) (u : D.what₂.Word) (τ : D.what₂.Tau) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h)
    {w0 : X.B.H (vOf X τ)} (hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) w0) :
    ∃ νq, Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h (sigB X (Qcs C τ) (Qics C τ) τ) w0
      (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ)
      (C.muW u τ) ((muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) (muGB X (Qcs C τ) (Qics C τ) τ) νq := by
  obtain ⟨hz, hT⟩ := zT C u τ
  have h2 := (transpC' C τ).2.1
  have hg := (transpC' C τ).2.2.1
  have hDS : IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) := by
    obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
    refine ⟨P, hP, ?_⟩
    exact dsHpk_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
      (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
      (X.B.lam (vOf X τ)) (lamD D τ)
      (fun i => by
        rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
        exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
      (X.B.σ (vOf X τ)) (X.ds (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg P hP
  have hμG := haar_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg
  have hμN := muNc_haar (D := D) hθ
  obtain ⟨νq, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExists _ _ _ hz hT _ _ hμG
    (isHaarOn_muS_gen hz hT (C.muW_haar u τ) (C.muW_one u τ) (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN))
  exact ⟨νq, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, hDS, hgap, hok, hlow, hz, hT, cStd_ne, hty_c C u τ,
    C.muW_haar u τ, hμN, hμG, hq⟩

end Formalism.L2.SG.RealObj.EnergyIntLoc
