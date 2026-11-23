import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConstCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCLineNonzero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesLeft
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

theorem line_at_most_one_holds : LineAtMost := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk Pr hPr π ζ hζ X hX Y hY hX0
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
  obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hGG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hcap : ∀ Z ∈ Line P Bs Pr π ζ, Gauge.GC.CapEig P Bs.π' (fun a => μ⁻¹ *ᵥ Fr a) π Z := by
    intro Z hZ Yc v
    have hZv : Pr π ν (Z v) = Z v := by
      have := DFunLike.congr_fun hZ.2 v
      simpa only [ContinuousLinearMap.comp_apply] using this
    have hr := ((hPr.2.2 ν hpos).2.2.2 π (Z v)).1 hZv Fr (by rw [hνfix]; exact hFr) (Yc + ((P.k : ℂ) - 2) / 2)
    rw [hpass Z hZ.1, hgl'] at hr
    have e : Yc + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Yc := by ring
    rw [e] at hr
    exact hr
  have hXF : X ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hX.1 (h, h') ⟨hh, hh', he⟩
  have hYF : Y ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hY.1 (h, h') ⟨hh, hh', he⟩
  exact Gauge.GC.lie_weight_at_most_holds Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hGG.ne' _ hFr' π X Y hXF hYF
    (hcap X hX) (hcap Y hY) hX0

theorem modConst_of_cut : ModConstOfCut := by
  intro hLN hAM hDT hSR hSN hTF Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  set x0 : ℝ := |P.TT| + 1 with hx0
  have hζ0 : ((x0 : ℝ) : ℂ) ∈ Gauge.GC.Ann P := by
    show P.TT < Complex.normSq ((x0 : ℝ) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith [abs_nonneg P.TT, le_abs_self P.TT]
  obtain ⟨X0, hX0F, hX0P, hX0ne⟩ := hLN Wp Wq P Bs hpl hk Pr hPr π _ hζ0
  set ζ0 : ℂ := ((x0 : ℝ) : ℂ) with hζ0def
  set T0 := (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)).comp
    (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)
      (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ0) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) X0) with hT0
  have hB0 : ‖B.hsVec X0‖ ≠ 0 := norm_ne_zero_iff.2 (Gauge.GC.hsVec_ne_zero hX0ne)
  refine ⟨M.Nrm P l π, ‖B.hsVec T0‖ ^ 2 / ‖B.hsVec X0‖ ^ 2, fun ζ hζ Xf hXf hXP => ⟨?_, ?_⟩⟩
  · have hL : Xf ∈ Line P Bs Pr π ζ := ⟨hXf, hXP⟩
    have hR := hSR Wp Wq P Bs hk X d hA l hl S hS Pr hPr π ρ hUp ζ hζ Xf hL
    rw [hR.2]
    exact hSN Wp Wq P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hL
  · have hζT : P.TT < Complex.normSq ζ := hζ
    have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
      rw [hTz, hTz']; exact hζT
    have hζ0T : P.TT < Complex.normSq ζ0 := hζ0
    have hζ0' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ0 := by
      rw [hTz, hTz']; exact hζ0T
    obtain ⟨h, hh, h', hh', hν, hν', hι, hst⟩ :=
      hDT P.k P.r Bs.z Bs.z' Bs.μsec hk hz hz' Bs.T_pos Bs.T'_pos Bs.sec ζ0 ζ hζ0' hζ'
    have hhi := LieBracketMultiplication.uw_inv hh
    have hh'i := LieBracketMultiplication.uw_inv hh'
    have hiso : ∀ Y, ‖B.hsVec ((Bs.π h).comp (Y.comp (Bs.π' h'⁻¹)))‖ = ‖B.hsVec Y‖ :=
      fun Y => CutBP.hsVec_norm_CinL Bs hh hh' Y
    have hinv1 : ∀ w, Bs.π h⁻¹ (Bs.π h w) = w := by
      intro w
      rw [← ContinuousLinearMap.comp_apply, ← Bs.π_rep.2 _ hhi _ hh, NFRadRedS.uw_inv_mul hh, Bs.π_rep.1]
      rfl

    have hF : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
      refine fun p hp => ?_
      have hp1 : p.1 ∈ UWset P.k P.r Bs.z := hp.1
      have hp2 : p.2 ∈ UWset P.k P.r Bs.z' := hp.2.1
      have hm1 : h⁻¹ * p.1 * h ∈ UWset P.k P.r Bs.z := LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul hhi hp1) hh
      have hm2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z' := LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul hh'i hp2) hh'
      have key := hX0F _ (hst p hp)
      have e1 : (Bs.π p.1).comp (Bs.π h) = (Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h)) := by
        rw [← Bs.π_rep.2 _ hp1 _ hh, ← Bs.π_rep.2 _ hh _ hm1, ← mul_assoc, ← mul_assoc,
          NFRadRedS.uw_mul_inv hh, one_mul]
      have e2 : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹) := by
        rw [← Bs.π'_rep.2 _ hh'i _ hp2, ← Bs.π'_rep.2 _ hm2 _ hh'i, mul_assoc (h'⁻¹ * p.2) h' h'⁻¹,
          NFRadRedS.uw_mul_inv hh', mul_one]
      ext v
      have k1 := DFunLike.congr_fun e1 (X0 (Bs.π' h'⁻¹ (Bs.π' p.2 v)))
      have k2 := DFunLike.congr_fun e2 v
      have k3 := DFunLike.congr_fun key (Bs.π' h'⁻¹ v)
      simp only [ContinuousLinearMap.comp_apply] at k1 k2 k3 ⊢
      rw [k1, k2, k3]

    have hP : (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp ((Bs.π h).comp (X0.comp (Bs.π' h'⁻¹))) =
        (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) := by
      rw [← hν, hPr.2.1 h hh π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)]
      ext v
      have k1 := DFunLike.congr_fun hX0P (Bs.π' h'⁻¹ v)
      simp only [ContinuousLinearMap.comp_apply] at k1 ⊢
      rw [hinv1, k1]
    have hL0 : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ∈ Line P Bs Pr π ζ := ⟨hF, hP⟩
    have hne : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ≠ 0 := by
      intro h0
      apply hB0
      have hz0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
        rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), Gauge.GC.hsVec_smul, zero_smul]
      rw [← hiso X0, h0, hz0, norm_zero]
    obtain ⟨c, hc⟩ := hAM Wp Wq P Bs hpl hk Pr hPr π ζ hζ _ hL0 Xf ⟨hXf, hXP⟩ hne

    have hTe := ((hTF Wp Wq P Bs hpl Bw Bw' hBw hBw').2.2.2.1 h hh h' hh'
      (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ0)
      (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) X0).1
    rw [hν, hν', hι] at hTe
    have hPT : (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
        (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
          (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
          ((Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)))) = (Bs.π h).comp (T0.comp (Bs.π' h'⁻¹)) := by
      rw [hTe]
      conv_lhs => rw [← hν]
      rw [hPr.2.1 h hh ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0), hT0]
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [hinv1]
    rw [hc, map_smul, ContinuousLinearMap.comp_smul, hPT, Gauge.GC.hsVec_smul, Gauge.GC.hsVec_smul,
      norm_smul, norm_smul, hiso, hiso]
    field_simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
