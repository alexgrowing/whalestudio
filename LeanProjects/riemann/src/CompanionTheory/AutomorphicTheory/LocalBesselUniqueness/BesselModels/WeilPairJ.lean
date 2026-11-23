import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.StepIntGOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.WeilPairJ

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.L2.SG.RealObj.EnergyIntOm Formalism.L2.SG.Pf.WuBL

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

namespace BM

variable {D : D7}

theorem weilPairJ (hI : CompanionTheory.Lime.BM.Inputs2) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hLF : ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), LocFactor C)
    (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : HidaSetting D) (τ : D.what₂.Tau) :
    ∃ (μS ν : D.what₂.Word → Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
      (∀ u, SFinite (μS u) ∧ SFinite (ν u) ∧
        (∀ f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable f →
          ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ x, ∫⁻ s, f (s * x) ∂(μS u) ∂(ν u)) ∧
        (μS u).map (fun x => x⁻¹) = μS u ∧ μS u (Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ))ᶜ = 0 ∧
        ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
            X.B.σ (vOf X τ) (uMat s) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u (vOf X τ) z'‖ₑ ∂(μS u) ∂(ν u) ∂(ν u) < ⊤ ∧
        (∀ s ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ), (μS u).map (fun x => s * x) = μS u) ∧ μS u ≠ 0) ∧
      ∀ (u u' : D.what₂.Word) (sc : ℝ), 0 < sc → ∀ cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u',
        ∀ g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
          Zhat (X.B.I.ε (vOf X τ)) (frm X u sc (vOf X τ)) (frm X u' sc (vOf X τ)) (uMat g) = Matrix.diagonal cv →
          ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
              X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
            ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u' (vOf X τ) z'‖ₑ ∂(μS u') ∂(μS u) ∂(ν u') ∂(ν u) < ⊤ := by
  rcases isEmpty_or_nonempty D.what₂.Word with hEW | hNW
  · exact ⟨fun _ => 0, fun _ => 0, fun u => isEmptyElim u, fun u => isEmptyElim u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
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
  set μNc := (muNB D 1).map (conjE (Formalism.L2.SG.Pf.muT_ne D)) with hμNc
  have hμN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) μNc := muNc_haar one_pos
  have sN : SigmaFinite (muNB D 1) :=
    (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D one_pos) (kapN_ne_top D 1)).1

  have hdat : ∀ u : D.what₂.Word, ∃ (l : X.B.H (vOf X τ) → X.Vloc u (vOf X τ)) (a : ℂ) (νq : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
      SFinite νq ∧
      Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h σc w0 (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd
        (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ) (C.muW u τ) μNc
        (muGB X (Qcs C τ) (Qics C τ) τ) νq ∧
      (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0, ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0,
        Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (piB X (Qcs C τ) (Qics C τ) u τ) σc (C.muW u τ) μNc x y =
          (innerSL ℂ (l y)).smulRight (l x)) ∧
      ∀ γ, X.Wloc u (vOf X τ) γ = a • l (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))) := by
    intro u
    obtain ⟨l, a, hbe, hW⟩ := Formalism.L2.SG.RealObj.EnergyIntQ.BM.locDDQ hI hRT hL2 hGp hG C (hLF D hG X 1 C) u τ
    obtain ⟨νq, hsf, hS⟩ := sideC_SF C one_pos u τ hgap hok hlow
    have hμW := C.muW_haar u τ
    have : SigmaFinite (C.muW u τ) := hμW.1
    refine ⟨l, a, νq, hsf, hS, fun x hx y hy => ?_, hW⟩
    rw [← scale_eq D, be_tor (Formalism.L2.SG.Pf.muT_ne D) (zT C u τ).1 (cS D) (piB X (C.Q τ) (C.Qi τ) u τ)
      (piB X (Qcs C τ) (Qics C τ) u τ) (sigB X (C.Q τ) (C.Qi τ) τ) σc (sigC_eq C τ)
      (fun _ hh => piC_eq C u τ hh) (C.muW u τ) (muNB D 1) hμW.2.2.1 x y]
    exact hbe x (dd_sub C τ hyc hx) y (dd_sub C τ hyc hy)
  choose l a νq hsf hS hl hW using hdat

  obtain ⟨hyiU, hyi⟩ := Formalism.MainNotions.S.Inh.unitary_group_inv_mem yc hyc
  set yi := Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * ycᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS with hyidef
  have hyi' : yc * yi = 1 := mul_eq_one_comm.mp hyi
  set yJ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) :=
    Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.ujOf _ (inUJ_tr (transpC' C τ) hyiU) with hyJ
  have hTyJ : Matrix.of (Tm C τ yJ) = yi := by
    show Qics C τ * uMat yJ * Qcs C τ = yi
    rw [hyJ, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.uMat_ujOf, show Qics C τ * (Qcs C τ * yi * Qics C τ) * Qcs C τ =
      (Qics C τ * Qcs C τ) * yi * (Qics C τ * Qcs C τ) by simp only [Matrix.mul_assoc], h1, Matrix.one_mul, Matrix.mul_one]
  have hTyJi : Matrix.of (Tm C τ yJ⁻¹) = yc := by
    rw [Tm_inv]
    show (Matrix.of (Tm C τ yJ))⁻¹ = yc
    rw [hTyJ]
    exact Matrix.inv_eq_right_inv hyi
  have key : ∀ x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), X.B.σ (vOf X τ) (uMat (x * yJ⁻¹)) (X.B.w (vOf X τ)) = σc (Matrix.of (Tm C τ x)) w0 := by
    intro x
    rw [← sigC_Tm C τ (x * yJ⁻¹), hw0, sigC_mul C τ (Tm_mem C τ x) hyc, Tm_mul]
    show σc (Matrix.of (Tm C τ x) * Matrix.of (Tm C τ yJ⁻¹)) (X.B.w (vOf X τ)) = _
    rw [hTyJi]
  have hWl : ∀ u (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), X.Wloc u (vOf X τ) (x * yJ⁻¹) = a u • l u (σc (Matrix.of (Tm C τ x)) w0) := by
    intro u x
    rw [hW u, key]
  have hsig : ∀ y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), X.B.σ (vOf X τ) (uMat y) = σc (Matrix.of (Tm C τ y)) := fun y =>
    (sigC_Tm C τ y).symm

  have hμGc := haar_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg
  have hSH : ∀ u, Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ))
      (Formalism.MainNotions.S.muS (C.muW u τ) μNc) := fun u =>
    isHaarOn_muS_gen (zT C u τ).1 (zT C u τ).2 (C.muW_haar u τ) (C.muW_one u τ)
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN)
  have hSc0 : ∀ u, Formalism.MainNotions.S.muS (C.muW u τ) μNc {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 := by
    intro u
    refine measure_mono_null ?_ (hSH u).2.2.1
    intro m hm
    simp only [Set.mem_ofPred_eq] at hm ⊢
    intro hmS
    apply hm
    obtain ⟨h0, hh0, n0, hn0, he⟩ := hmS
    rw [he]
    exact Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hh0.1 hn0.1
  have hνc0 : ∀ u, νq u {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 := fun u =>
    quot_conc (hS u).2.2.2.2.2.2.2.2.2.2.2.2 hμGc.2.2.1 (hSc0 u) (hSH u).2.1
  have hcm : ∀ (c : ℝ≥0∞), c ≠ ⊤ → ∀ (μ : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) (f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞),
      ∫⁻ x, c * f x ∂μ = c * ∫⁻ x, f x ∂μ := fun c hc μ f => lintegral_const_mul' c f hc
  refine ⟨fun u => (Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ),
    fun u => ((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹), fun u => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := (hSH u).1
    have := sigmaFinite_comap C τ (hSc0 u)
    infer_instance
  · have := hsf u
    have := sFinite_comap C τ (μ := νq u)
    infer_instance
  · intro f hf
    have hf' : Measurable (fun y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => f (y * yJ⁻¹)) := hf.comp (measurable_mul_const _)
    have hq : Formalism.MainNotions.S.IsQuotMeas (muGB X (Qcs C τ) (Qics C τ) τ) (Formalism.MainNotions.S.muS (C.muW u τ) μNc) (νq u) :=
      (hS u).2.2.2.2.2.2.2.2.2.2.2.2
    rw [lintegral_map_equiv]
    calc ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
        = ∫⁻ x, f (x * yJ⁻¹) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by
          rw [← lintegral_map hf (measurable_mul_const yJ⁻¹), Formalism.REAL.indefinite_unitary_unimodular _ _ yJ⁻¹]
      _ = _ := weil_J C τ hq (hSc0 u) (hνc0 u) _ hf'
      _ = _ := by
          refine lintegral_congr fun x => lintegral_congr fun s => ?_
          simp only [MeasurableEquiv.coe_mulRight, mul_assoc]
  · exact inv_comap C τ (hSc0 u) (muS_inv (zT C u τ).1 (zT C u τ).2
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zT C u τ).1 (zT C u τ).2 (C.muW_haar u τ))
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN))
  · rw [(Tm_emb C τ).comap_apply]
    refine measure_mono_null ?_ (hSH u).2.2.1
    rintro _ ⟨x, hx, rfl⟩ hxs
    exact hx (sloc_of_sset C τ u x hxs)
  ·
    have hint := (CompanionTheory.D.Upq.BesselFunctionalConstruction.quadConv CompanionTheory.Lime.BM.inputs D.R.k D.R.rS _ _ (Dc C one_pos u u τ) (epsSH D.R) (lamD D τ) h _
      σc w0 _ _ (νq u) (νq u) (hS u) (hS u) (l u) (l u) (hl u) (hl u)).2
    have e : ∀ x x' s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
        ‖⟪X.B.σ (vOf X τ) (uMat (x * yJ⁻¹)) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat s) (X.B.σ (vOf X τ) (uMat (x' * yJ⁻¹)) (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) (x * yJ⁻¹)‖ₑ * ‖X.Wloc u (vOf X τ) (x' * yJ⁻¹)‖ₑ =
        (‖a u‖ₑ * ‖a u‖ₑ) * (((‖⟪σc (Matrix.of (Tm C τ x)) w0, σc (Matrix.of (Tm C τ s))
          (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) * ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞)) := by
      intro x x' s
      rw [key, key, hsig s, hWl, hWl, enorm_smul, enorm_smul]
      show _ * (‖a u‖ₑ * ‖l u (σc (Matrix.of (Tm C τ x)) w0)‖ₑ) * (‖a u‖ₑ * ‖l u (σc (Matrix.of (Tm C τ x')) w0)‖ₑ) = _
      simp only [enorm]
      ring
    have step : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat s)
        (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ * ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u (vOf X τ) z'‖ₑ
          ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ))
          ∂(((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹))
          ∂(((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹)) =
        (‖a u‖ₑ * ‖a u‖ₑ) * ∫⁻ x, ∫⁻ x', ∫⁻ s, (((‖⟪σc (Matrix.of (Tm C τ x)) w0, σc (Matrix.of (Tm C τ s))
          (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) * ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞))
          ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)) ∂((νq u).comap (Tm C τ)) ∂((νq u).comap (Tm C τ)) := by
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x => ?_
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x' => ?_
      rw [← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun s => ?_
      exact e x x' s
    rw [step]
    have hL := lintegral_three_comap C τ (hνc0 u) (hSc0 u) (fun m m' p => ((‖⟪σc (Matrix.of m) w0, σc (Matrix.of p)
          (σc (Matrix.of m') w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) * ((‖l u (σc (Matrix.of m) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of m') w0)‖₊ : NNReal) : ℝ≥0∞))
    beta_reduce at hL
    rw [hL]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) hint
  · intro s hs
    have hmap : ((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)).map (Tm C τ) = Formalism.MainNotions.S.muS (C.muW u τ) μNc := by
      rw [(Tm_emb C τ).map_comap, Measure.restrict_eq_self_of_ae_mem]
      rw [ae_iff]
      refine measure_mono_null (fun m hm => ?_) (hSc0 u)
      simp only [Set.mem_ofPred_eq] at hm ⊢
      exact fun h => hm (mem_range_Tm C τ h)
    have hTs := sset_of_sloc C τ u s hs
    have hleft := (hSH u).2.2.2 _ hTs
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) (Matrix.of (Tm C τ s))) :=
      (Formalism.MainNotions.BridgeCSB.continuous_lmulM _).measurable
    have hcomm : Tm C τ ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (Matrix.of (Tm C τ s)) ∘ Tm C τ := by
      funext y
      exact Tm_mul C τ s y
    rw [← (Tm_emb C τ).comap_map (((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)).map (fun x => s * x)),
      Measure.map_map (Tm_emb C τ).measurable (measurable_const_mul s), hcomm,
      ← Measure.map_map hlm (Tm_emb C τ).measurable, hmap, hleft]
  · intro h0
    beta_reduce at h0
    have hmap : ((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)).map (Tm C τ) = Formalism.MainNotions.S.muS (C.muW u τ) μNc := by
      rw [(Tm_emb C τ).map_comap, Measure.restrict_eq_self_of_ae_mem]
      rw [ae_iff]
      refine measure_mono_null (fun m hm => ?_) (hSc0 u)
      simp only [Set.mem_ofPred_eq] at hm ⊢
      exact fun h => hm (mem_range_Tm C τ h)
    apply (hSH u).2.1
    rw [← hmap, h0, Measure.map_zero]
  ·
    intro u u' sc hsc cv hcv g hgd
    have hom := mem_om_loc (Formalism.L2.SG.Pf.cfS_ne D) (transpC' C τ) hsc u u' cv hcv g hgd
    rw [zc_eq, zc_eq] at hom
    set γc := Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) g with hγc
    have hint := (CompanionTheory.D.Upq.BesselFunctionalConstruction.quadConv CompanionTheory.Lime.BM.inputs D.R.k D.R.rS _ _ (Dc C one_pos u u' τ) (epsSH D.R) (lamD D τ) h _
      σc w0 _ _ (νq u) (νq u') (hS u) (hS u') (l u) (l u') (hl u) (hl u')).1 γc hom
    have hsg : ∀ s s' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
        X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) = σc (Matrix.of (Tm C τ s) * γc * (Matrix.of (Tm C τ s'))⁻¹) := by
      intro s s'
      rw [hsig, Tm_mul, Tm_mul, Tm_inv]
      rfl
    have e : ∀ x x' s s' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
        ‖⟪X.B.σ (vOf X τ) (uMat (x * yJ⁻¹)) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹))
          (X.B.σ (vOf X τ) (uMat (x' * yJ⁻¹)) (X.B.w (vOf X τ)))⟫_ℂ‖ₑ * ‖X.Wloc u (vOf X τ) (x * yJ⁻¹)‖ₑ * ‖X.Wloc u' (vOf X τ) (x' * yJ⁻¹)‖ₑ =
        (‖a u‖ₑ * ‖a u'‖ₑ) * (((‖⟪σc (Matrix.of (Tm C τ x)) w0,
          σc (Matrix.of (Tm C τ s) * γc * (Matrix.of (Tm C τ s'))⁻¹) (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u' (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞)) := by
      intro x x' s s'
      rw [key, key, hsg, hWl, hWl, enorm_smul, enorm_smul]
      show _ * (‖a u‖ₑ * ‖l u (σc (Matrix.of (Tm C τ x)) w0)‖ₑ) * (‖a u'‖ₑ * ‖l u' (σc (Matrix.of (Tm C τ x')) w0)‖ₑ) = _
      simp only [enorm]
      ring
    have step : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
        X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u' (vOf X τ) z'‖ₑ
          ∂((Formalism.MainNotions.S.muS (C.muW u' τ) μNc).comap (Tm C τ)) ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ))
          ∂(((νq u').comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹))
          ∂(((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹)) =
        (‖a u‖ₑ * ‖a u'‖ₑ) * ∫⁻ x, ∫⁻ x', ∫⁻ s, ∫⁻ s', (((‖⟪σc (Matrix.of (Tm C τ x)) w0,
          σc (Matrix.of (Tm C τ s) * γc * (Matrix.of (Tm C τ s'))⁻¹) (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u' (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞))
          ∂((Formalism.MainNotions.S.muS (C.muW u' τ) μNc).comap (Tm C τ)) ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ))
          ∂((νq u').comap (Tm C τ)) ∂((νq u).comap (Tm C τ)) := by
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x => ?_
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x' => ?_
      rw [← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun s => ?_
      rw [← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun s' => ?_
      exact e x x' s s'
    rw [step]
    have hL := lintegral_four_comap C τ (hνc0 u) (hνc0 u') (hSc0 u) (hSc0 u') (fun m m' p p' => ((‖⟪σc (Matrix.of m) w0,
          σc (Matrix.of p * γc * (Matrix.of p')⁻¹) (σc (Matrix.of m') w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of m) w0)‖₊ : NNReal) : ℝ≥0∞) * ((‖l u' (σc (Matrix.of m') w0)‖₊ : NNReal) : ℝ≥0∞))
    beta_reduce at hL
    rw [hL]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) hint

end BM

end Formalism.L2.SG.RealObj.EnergyConvJ
