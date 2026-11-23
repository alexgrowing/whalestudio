import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocDDQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UMatInvMul

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.Pf.WuBL

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntLoc

namespace BM

variable {k r : ℕ}

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem locOrbG_of (hI : CompanionTheory.Lime.BM.Inputs2) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hLF : ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), LocFactor C) :
    Formalism.L2.SG.RealObj.EnergyInt.LocOrbG := by
  intro D hG X u u' sc hsc c hc γ hγ v
  obtain ⟨τ, rfl⟩ : ∃ τ, v = vOf X τ := ⟨X.pl v, (X.pl.symm_apply_apply v).symm⟩
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  obtain ⟨l, a, hbe, hW⟩ := Formalism.L2.SG.RealObj.EnergyIntQ.BM.locDDQ hI hRT hL2 hGp hG C (hLF D hG X 1 C) u τ
  obtain ⟨l', a', hbe', hW'⟩ := Formalism.L2.SG.RealObj.EnergyIntQ.BM.locDDQ hI hRT hL2 hGp hG C (hLF D hG X 1 C) u' τ
  have h1 := (transpC' C τ).1
  have h2 := (transpC' C τ).2.1
  have hg := (transpC' C τ).2.2.1
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
  obtain ⟨yc, hyc, hycl⟩ := y_exists (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
    (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
    (X.B.lam (vOf X τ)) (lamD D τ)
    (fun i => by
      rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
      exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
    (X.B.σ (vOf X τ)) (X.ds (vOf X τ)).2.2.1 (X.low (vOf X τ)).2 (Qcs C τ) (Qics C τ) h2 hg P hP
  set σc := sigB X (Qcs C τ) (Qics C τ) τ with hσc
  set w0 := σc yc (X.B.w (vOf X τ)) with hw0
  have hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) σc w0 := by
    refine ⟨P, hP, ?_, hycl⟩
    rw [hw0, sigC_norm C τ hyc]
    exact (X.low (vOf X τ)).1
  obtain ⟨h, hgap, hok⟩ := hGp D hG τ
  obtain ⟨νq, hS⟩ := sideC C one_pos u τ hgap hok hlow
  obtain ⟨νq', hS'⟩ := sideC C one_pos u' τ hgap hok hlow
  have hμW := C.muW_haar u τ
  have hμW' := C.muW_haar u' τ
  have : SigmaFinite (C.muW u τ) := hμW.1
  have : SigmaFinite (C.muW u' τ) := hμW'.1
  have : SigmaFinite (muNB D 1) :=
    (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D one_pos) (kapN_ne_top D 1)).1

  have hl : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0, ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0,
      Formalism.FourierDecayAlt.ThreeDimData.be (Dc C one_pos u u' τ).z Formalism.QuantumDeterminants.cStd (Dc C one_pos u u' τ).π σc (Dc C one_pos u u' τ).μW
        (Dc C one_pos u u' τ).μN x y = (innerSL ℂ (l y)).smulRight (l x) := by
    intro x hx y hy
    show Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (piB X (Qcs C τ) (Qics C τ) u τ) σc (C.muW u τ)
      ((muNB D 1).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) x y = _
    rw [← scale_eq D, be_tor (Formalism.L2.SG.Pf.muT_ne D) (zT C u τ).1 (cS D) (piB X (C.Q τ) (C.Qi τ) u τ)
      (piB X (Qcs C τ) (Qics C τ) u τ) (sigB X (C.Q τ) (C.Qi τ) τ) σc (sigC_eq C τ)
      (fun _ hh => piC_eq C u τ hh) (C.muW u τ) (muNB D 1) hμW.2.2.1 x y]
    exact hbe x (dd_sub C τ hyc hx) y (dd_sub C τ hyc hy)
  have hl' : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0, ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0,
      Formalism.FourierDecayAlt.ThreeDimData.be (Dc C one_pos u u' τ).z' Formalism.QuantumDeterminants.cStd (Dc C one_pos u u' τ).π' σc (Dc C one_pos u u' τ).μW'
        (Dc C one_pos u u' τ).μN x y = (innerSL ℂ (l' y)).smulRight (l' x) := by
    intro x hx y hy
    show Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u' τ) Formalism.QuantumDeterminants.cStd (piB X (Qcs C τ) (Qics C τ) u' τ) σc (C.muW u' τ)
      ((muNB D 1).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) x y = _
    rw [← scale_eq D, be_tor (Formalism.L2.SG.Pf.muT_ne D) (zT C u' τ).1 (cS D) (piB X (C.Q τ) (C.Qi τ) u' τ)
      (piB X (Qcs C τ) (Qics C τ) u' τ) (sigB X (C.Q τ) (C.Qi τ) τ) σc (sigC_eq C τ)
      (fun _ hh => piC_eq C u' τ hh) (C.muW u' τ) (muNB D 1) hμW'.2.2.1 x y]
    exact hbe' x (dd_sub C τ hyc hx) y (dd_sub C τ hyc hy)

  set γc := Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) (γ (vOf X τ)) with hγc
  have hom := Formalism.L2.SG.RealObj.EnergyIntOm.mem_om X (Formalism.L2.SG.Pf.cfS_ne D) (transpC' C τ) hsc u u' c hc γ hγ
  rw [zc_eq, zc_eq] at hom
  have hint := CompanionTheory.D.Upq.BesselFunctionalConstruction.ooConv CompanionTheory.Lime.BM.inputs D.R.k D.R.rS _ _ (Dc C one_pos u u' τ) (epsSH D.R) (lamD D τ) h _ σc w0
    _ _ νq νq' hS hS' l l' hl hl' γc hom

  set μGc := muGB X (Qcs C τ) (Qics C τ) τ with hμGc
  set F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞ :=
    fun m => ‖l (σc (Matrix.of m) w0)‖ₑ * ‖l' (σc (γc⁻¹ * Matrix.of m) w0)‖ₑ with hF
  have hFfin : ∫⁻ m, F m ∂μGc < ⊤ := by
    have hfi := hint.2
    unfold HasFiniteIntegral at hfi
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun m => ?_)) hfi
    simp only [hF]
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]
  clear_value F μGc

  obtain ⟨hyiU, hyi⟩ := Formalism.MainNotions.S.Inh.unitary_group_inv_mem yc hyc
  set yi := Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * ycᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS with hyidef
  have hyi' : yc * yi = 1 := mul_eq_one_comm.mp hyi
  have hR : ∫⁻ m, F (Formalism.FourierDecayAlt.B.rmulF yi m) ∂μGc = ∫⁻ m, F m ∂μGc := by
    have hrm : μGc.map (Formalism.FourierDecayAlt.B.rmulF yi) = μGc := by
      rw [hμGc]
      exact (Formalism.L2.SG.Pf.BaseOf.haarG_B (n_eq' X) (X.B.I.ε (vOf X τ)) h2 hg).right yi hyiU
    rw [← rmulE_coe yi yc hyi hyi', ← lintegral_map_equiv F (rmulE yi yc hyi hyi'), rmulE_coe, hrm]

  have hTe : MeasurableEmbedding (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (vOf X τ)) h2).measurableEmbedding
  have hCV : ∫⁻ x, F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)))
      ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ m, F (Formalism.FourierDecayAlt.B.rmulF yi m) ∂μGc := by
    rw [hμGc]
    unfold muGB
    exact (hTe.lintegral_map (fun m => F (Formalism.FourierDecayAlt.B.rmulF yi m))).symm

  have key : ∀ x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
      σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) w0 = X.B.σ (vOf X τ) (uMat x) (X.B.w (vOf X τ)) := by
    intro x
    have hTx := Formalism.L2.SG.Pf.LTL.trG_mem (Qcs C τ) (Qics C τ) _ h2 hg x
    rw [hw0, sigC_mul C τ (Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hTx hyiU) hyc, Matrix.mul_assoc, hyi, Matrix.mul_one]
    show X.B.σ (vOf X τ) (Qcs C τ * (Qics C τ * uMat x * Qcs C τ) * Qics C τ) (X.B.w (vOf X τ)) = _
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hγinv : γc⁻¹ = Qics C τ * uMat (γ (vOf X τ))⁻¹ * Qcs C τ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hγc]
    unfold Formalism.L2.SG.RealObj.trG
    calc Qics C τ * uMat (γ (vOf X τ))⁻¹ * Qcs C τ * (Qics C τ * uMat (γ (vOf X τ)) * Qcs C τ)
        = Qics C τ * (uMat (γ (vOf X τ))⁻¹ * (Qcs C τ * Qics C τ) * uMat (γ (vOf X τ))) * Qcs C τ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, uMat_inv_mul', Matrix.mul_one, h1]
  have hpt : ∀ x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
      ‖X.Wloc u (vOf X τ) x‖ₑ * ‖X.Wloc u' (vOf X τ) ((γ (vOf X τ))⁻¹ * x)‖ₑ =
        (‖a‖ₑ * ‖a'‖ₑ) * F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x))) := by
    intro x
    have e2 : γc⁻¹ * Matrix.of (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x))) =
        Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) ((γ (vOf X τ))⁻¹ * x) * yi := by
      show γc⁻¹ * (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) = _
      rw [hγinv]
      unfold Formalism.L2.SG.RealObj.trG
      rw [uMat_mul']
      calc Qics C τ * uMat (γ (vOf X τ))⁻¹ * Qcs C τ * (Qics C τ * uMat x * Qcs C τ * yi)
          = Qics C τ * uMat (γ (vOf X τ))⁻¹ * (Qcs C τ * Qics C τ) * uMat x * Qcs C τ * yi := by
            simp only [Matrix.mul_assoc]
        _ = Qics C τ * (uMat (γ (vOf X τ))⁻¹ * uMat x) * Qcs C τ * yi := by
            rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hW x, hW' ((γ (vOf X τ))⁻¹ * x), enorm_smul, enorm_smul, ← key x, ← key ((γ (vOf X τ))⁻¹ * x)]
    simp only [hF]
    rw [e2]
    show ‖a‖ₑ * ‖l (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) w0)‖ₑ *
        (‖a'‖ₑ * ‖l' (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) ((γ (vOf X τ))⁻¹ * x) * yi) w0)‖ₑ) =
      ‖a‖ₑ * ‖a'‖ₑ * (‖l (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) w0)‖ₑ *
        ‖l' (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) ((γ (vOf X τ))⁻¹ * x) * yi) w0)‖ₑ)
    ring
  calc ∫⁻ x, ‖X.Wloc u (vOf X τ) x‖ₑ * ‖X.Wloc u' (vOf X τ) ((γ (vOf X τ))⁻¹ * x)‖ₑ
        ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
      = ∫⁻ x, (‖a‖ₑ * ‖a'‖ₑ) *
          F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)))
          ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_congr hpt
    _ = (‖a‖ₑ * ‖a'‖ₑ) * ∫⁻ x,
          F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)))
          ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)
    _ < ⊤ := by
        rw [hCV, hR]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) hFfin

theorem stepIntG_of (hI : CompanionTheory.Lime.BM.Inputs2) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hLF : ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), LocFactor C) :
    Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyInt.stepIntG_of_loc (Formalism.L2.SG.RealObj.EnergyIntLoc.BM.locOrbG_of hI hRT hL2 hGp hLF)

end BM

end Formalism.L2.SG.RealObj.EnergyIntLoc
