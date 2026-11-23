import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SsetOfSloc
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.L2.SG.RealObj.EnergyIntOm Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal Classical

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem mem_om_loc {v : InfinitePlace X.B.I.F} {lam : ℂ} (hl : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : 0 < sc) (u u' : D.what₂.Word) (cv : Fin (D.R.rS + 1) → ℂ)
    (hcv : cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u') (g : Formalism.REAL.UJ (X.B.I.ε v))
    (hg : Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal cv) :
    trG Q Qi g ∈ Formalism.FourierDecayAlt.JF.Om D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) := by
  have hsc0 : sc ≠ 0 := hsc.ne'
  set γ : X.B.I.Ginf := Function.update (1 : X.B.I.Ginf) v g with hγdef
  have hγv : γ v = g := by rw [hγdef]; exact Function.update_self _ _ _
  obtain ⟨d, hd⟩ : ∃ d : Fin (D.R.rS + 1) → ℂ, d = fun a => star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a * cv a :=
    ⟨_, rfl⟩
  have hZ : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
      (trG Q Qi g) = Matrix.diagonal d := by
    ext a b
    have := zhat_tr X hQ hsc0 u u' γ a b
    rw [hγv] at this
    rw [this]
    have hZX : ZX X u u' sc γ v = Matrix.diagonal cv := by
      unfold ZX; rw [hγv]; exact hg
    rw [hZX]
    by_cases hab : a = b
    · subst hab; simp [hd]
    · simp [Matrix.diagonal_apply_ne _ hab]
  have hd0 : ∀ a, d a ≠ 0 := fun a => by
    rw [hd]; exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr (dsc_ne hl hsc0 a)) (dsc_ne hl hsc0 a)) (hcv.1 a)
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem Q Qi _ hQ.2.1 hQ.2.2.1 g, fun l _ => ?_, ?_⟩
  · rw [dmin_diag _ _ _ d hZ l]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
  · unfold Formalism.QuantumDeterminants.Gf
    rw [dmin_diag _ _ _ d hZ, dmin_diag _ _ _ d hZ,
      (show Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) = Tw u from (Formalism.L2.SG.Pf.Choice.zTr_of X hQ u).2),
      (show Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) = Tw u' from (Formalism.L2.SG.Pf.Choice.zTr_of X hQ u').2)]
    have hlast := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.normSq_last_gt (Tw u) (Tw u') cv hcv.2
    have hcl : ∀ (h : D.R.rS + 1 ≤ D.R.rS + 1) (i : Fin (D.R.rS + 1)), Fin.castLE h i = i := fun _ _ => Fin.ext rfl
    have hdl : d (Fin.last D.R.rS) = cv (Fin.last D.R.rS) := by simp only [hd, dsc_last, star_one, one_mul]
    obtain ⟨P, hPd⟩ : ∃ P : ℂ, P = ∏ i : Fin D.R.rS, d (Fin.castSucc i) := ⟨_, rfl⟩
    have e1 : ∏ i : Fin (Fin.last (D.R.rS + 1)).val, d (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt) i) =
        P * cv (Fin.last D.R.rS) := by
      show ∏ i : Fin (D.R.rS + 1), d (Fin.castLE _ i) = _
      rw [Fin.prod_univ_castSucc]
      simp only [hcl, hdl, hPd]
    have e2 : ∏ i : Fin (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).val,
        d (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt) i) = P := by
      rw [hPd]; rfl
    rw [e1, e2]
    have hP0 : P ≠ 0 := by rw [hPd]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
    rw [Complex.normSq_mul]
    have hn : Tw u * Tw u' < Complex.normSq (cv (Fin.last D.R.rS)) := by
      rw [Complex.normSq_eq_norm_sq]; exact hlast
    have hp : 0 < Complex.normSq P := Complex.normSq_pos.mpr hP0
    nlinarith

theorem sideC_SF (C : Choice X θ) (hθ : 0 < θ) (u : D.what₂.Word) (τ : D.what₂.Tau) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h)
    {w0 : X.B.H (vOf X τ)} (hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) w0) :
    ∃ νq, SFinite νq ∧ Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h (sigB X (Qcs C τ) (Qics C τ) τ) w0
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
  obtain ⟨νq, hsf, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExistsSF _ _ _ hz hT _ _ hμG
    (isHaarOn_muS_gen hz hT (C.muW_haar u τ) (C.muW_one u τ) (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN))
  exact ⟨νq, hsf, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, hDS, hgap, hok, hlow, hz, hT, cStd_ne, hty_c C u τ,
    C.muW_haar u τ, hμN, hμG, hq⟩

end Formalism.L2.SG.RealObj.EnergyConvJ
