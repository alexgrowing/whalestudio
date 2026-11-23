import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBChain
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmplitudeBoundsAllChoicesUniform

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.BDatR
  Formalism.L2.SG.ThmBUseR Formalism.L2.SG.Pf.JointAmplitudePoints Formalism.L2.SG.Pf.ThmBChain
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChainG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem jointAmplitudeRotated_generic (Y : Full X) (u : D.what₂.Word) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ} (C : Choice X θ)
    (hB : WuBessel C) (ν νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ)
    (hR : RelPtExPR u u C) (hM : RMeasExP u u C) (hP : LocalAmplitudesPositive Y u u ν C hB) (hT : ThetaWinP Y u u ν C hB large₂ C1) :
    JointAmplitudeFactorizationRotated (genT (Y.tO u u)) (NOfG Y u νL ν ng) large₂ C1 (WX C u u) (AX hB u u) (D.mem u).A.T (D.mem u).A.T 1 := by
  intro γ w _ hw hb hJ
  subst hw
  have hJ' : 0 < J2of Y u u ν (toPts w) := hJ
  obtain ⟨w', hw', g0, hg0⟩ := isPtRep_of_J2of hJ'
  have hw'w : w' = w := toPts_injective hw'
  subst hw'w
  have hrep : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w' g := ⟨g0, hg0⟩
  have hP1 := hP w' hb hJ'
  set J2 := J2of Y u u ν (toPts w') with hJ2
  set th := thetaP u u hB J2 w' with hth
  have hthv : th = (localAmplitudeProduct u u hB w' / J2) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    rw [hth]; unfold thetaP; rw [if_pos ⟨hJ', hP1⟩]
  have hth0 : 0 < th := by rw [hthv]; exact Real.rpow_pos_of_pos (div_pos hP1 hJ') _
  have hfc : (0 : ℝ) < 2 * Fintype.card D.what₂.Tau := by
    have := card_pos' D; positivity
  have hpow : th ^ (2 * Fintype.card D.what₂.Tau) = localAmplitudeProduct u u hB w' / J2 := by
    rw [hthv, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hP1 hJ').le]
    push_cast
    rw [one_div_mul_cancel hfc.ne', Real.rpow_one]
  refine ⟨gamP C u u w', fun _ => th, fun τ => (ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ, fun τ => ?_, ?_⟩
  · have hnu : ∃ ν₁, RMeas D (locW C u u τ) (gamP C u u w' τ) 1 ν₁ := hM w' hb hrep τ
    have hnuP : nu1P C u u w' τ = hnu.choose := by unfold nu1P; rw [dif_pos hnu]
    refine ⟨hR w' hb hrep τ, hT w' hb hJ', ?_⟩
    obtain ⟨p, μR, hR1, hQ⟩ := hnu.choose_spec
    refine ⟨p, μR, hR1, ?_⟩
    show IsQuotMeas _ (ENNReal.ofReal th • μR) ((ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ)
    rw [hnuP]
    have hQ' : IsQuotMeas (WX C u u τ).μG μR hnu.choose := by
      simpa [ENNReal.ofReal_one, one_smul] using hQ
    exact Formalism.L2.SG.Pf.LTL.isQuotMeas_smul hQ' (by simpa using hth0) ENNReal.ofReal_ne_top
  · have hloc : ∀ τ, hsNormSq ((AX hB u u τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ)
        (gamP C u u w' τ)) = (th ^ 2)⁻¹ *
          hsNormSq ((locS hB u u τ).J (nu1P C u u w' τ) (gamP C u u w' τ)) := by
      intro τ
      rw [Formalism.L2.SG.Pf.LTL.locJ_smul, Formalism.L2.SG.Pf.LTL.hsNormSq_smul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hth0.le, Complex.normSq_ofReal]
      congr 1
      rw [sq, mul_inv]
    have hprod : ∏ τ, hsNormSq ((AX hB u u τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ)
        (gamP C u u w' τ)) = J2 := by
      rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      change ((th ^ 2)⁻¹) ^ Fintype.card D.what₂.Tau * localAmplitudeProduct u u hB w' = J2
      rw [inv_pow, ← pow_mul, hpow]
      field_simp
    have hnn : ∀ τ, 0 ≤ hsNormSq ((AX hB u u τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ)
        (gamP C u u w' τ)) := fun τ => Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg _
    rw [ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_prod_of_nonneg (fun τ _ => hnn τ), hprod]
    exact le_rfl

theorem rowBDataGR_of_rest {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word}
    {ν : X.B.I.Ginf → Measure X.B.I.Ginf} {C1 Cn Ire : ℝ} (h : RowRestR large₂ Y u u ν C1 Cn Ire) :
    RowBDataGR large₂ Y u ν C1 Cn Ire := by
  obtain ⟨hIre, θ, C, hB, h0, hw, hl, hM, hP, hT, hN⟩ := h
  exact ⟨hIre, θ, C, hB, h0, hw, hl, 1, zero_le_one,
    fun νL ng => jointAmplitudeRotated_generic Y u large₂ C1 C hB ν νL ng (Formalism.L2.SG.Pf.RelPtR.relPtExPR_holds C u u) hM hP hT,
    fun sec hs => by rw [ENNReal.ofReal_one, one_mul]; exact hN sec hs⟩

theorem rowBDataUnifGR_of (h : RowRestUnifR) : RowBDataUnifGR := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, Cn, a, b, h2⟩ := h Cg cb Cw cT CT C0
  exact ⟨C1, Cn, a, b, fun C' Cl h1 h3 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp =>
    rowBDataGR_of_rest (h2 C' Cl h1 h3 D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp)⟩

end Formalism.L2.SG.Pf.ThmBChainG

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.ThmBChainG

theorem theoremB_generic_final (hB : JointNormBoundRotatedUniform) (hA : AmpUnif) (hR : RowRestUnifR) : StepThmBG :=
  stepThmBG_ofR hB hA Formalism.L2.SG.PointUniformity.ptUnifG (rowBDataUnifGR_of hR)

end Formalism.L2.SG.Pf
