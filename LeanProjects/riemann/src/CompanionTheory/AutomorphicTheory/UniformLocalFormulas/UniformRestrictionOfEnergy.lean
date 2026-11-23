import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.HilbertSchmidtDiagonalInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmplitudeBoundsAllChoicesUniform
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinJF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBTheta
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyJSZ
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos

noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.RealObj Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.ThmBChain6

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def UniqOfPin : Prop :=
  ∀ (D : D7), ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))),
    (∀ w, JointQuot.OkPt X u u' w → JointQuot.LocPin X u u' w νl) → LocNorm.LocUniqP u u' C hB νl

def EnergyFin : Prop :=
  ∀ (D : D7), ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word), intCe X u u' 1 ≠ ⊤

theorem norm_eq {D : D7} {X : HidaSetting D} {θ : ℝ} (Y : Full X) (C : Choice X θ) (hB : WuBessel C) (hLF : LocFactor C)
    (u u' : D.what₂.Word) (hfin : intCe X u u' 1 ≠ ⊤) {c c' Irat Ire : ℝ}
    (hc : c = (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal / (Module.finrank ℂ (X.Vpi u) : ℝ))
    (hc' : c' = (X.muN u' (Y.FN u')).toReal * (X.muH u' Set.univ).toReal / (Module.finrank ℂ (X.Vpi u') : ℝ))
    (hcc : c * c' ≠ 0) (h1 : (c * c')⁻¹ * IntC X u u' 1 = 2 ^ (D.R.f * (D.R.rS + 1)) * Irat)
    (h2 : Irat = Formalism.FourierDecayAlt.PN.abelian₂ D.host.rdE D.R.rS D.R.k D.R.f *
      D.host.rdE ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) * Ire)
    {sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hsec : ∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (sec τ)) :
    ∏ τ, MMv D u u' (locS hB u u' τ) (sec τ) =
      ENNReal.ofReal (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' * Ire) := by
  have hV := AmpWinJF.levelVolume_pos (X := X)
  have hA : (∏ τ, AmpWin.kap u u' C hB τ) * (c * c') = LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' := by
    have h := AmpWinGlob.ampWin_of_loc C u Y u' hLF hB
    unfold AmpWin.AmpWinP PoincareInHH.PoincareSetting.c0X at h
    refine mul_left_cancel₀ (pow_pos hV 2).ne' ?_
    rw [← h, hc, hc']
    ring
  have hK : 0 < Kpl D ^ D.R.f := pow_pos (kpl_pos D) _
  have hI : IntC X u u' 1 = c * c' * (Kpl D ^ D.R.f * Ire) := by
    rw [kpl_pow, mul_assoc (2 ^ _), ← h2, ← h1, ← mul_assoc, mul_inv_cancel₀ hcc, one_mul]
  have hE := energy_prod C hB u u' hsec
  have hk0 : 0 ≤ ∏ τ, AmpWin.kap u u' C hB τ := Finset.prod_nonneg fun τ _ => Complex.normSq_nonneg _
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_pow (kpl_pos D).le] at hE
  have e : (∏ τ, AmpWin.kap u u' C hB τ) * (intCe X u u' 1).toReal =
      Kpl D ^ D.R.f * (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' * Ire) := by
    rw [← hA]
    show _ * IntC X u u' 1 = _
    rw [hI]; ring
  rw [e, ENNReal.ofReal_mul hK.le] at hE
  exact ((ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hK).ne' ENNReal.ofReal_ne_top).1 hE).symm

theorem uniform_restriction_of_energy (hF : LoopBCovN.CovNFormula) (hU : UniqOfPin) (hE : EnergyFin) : AmplitudeBoundsAllChoicesUniform := by
  intro Cg cb Cw cT CT C0
  obtain ⟨Cgs, CTs, -, -, a, b, hS⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  refine ⟨1, 1, max a 29, max b 16, fun C' Cl h1 h3 D large₂ X Y u u' hc hb X0 ψ _ sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire
    hO ν hp => ?_⟩
  have hG : ConcreteSettingExists.GapHyp D :=
    ThmSOwn.gap_hypothesis_of_hypotheses hc.1.1 (le_trans (le_max_right _ _) h3) (le_trans (le_max_right _ _) h1)
  obtain ⟨-, hb16, hrd0, hrdb, -⟩ := hS C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h3) D large₂ X Y u u' hc
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  obtain ⟨-, -, hNI, -, -, -, hF1, hF2⟩ := hO
  have hP := hNI.1
  set B := bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq with hBdef
  have hc0 : 0 < B.c0 * B.c0' := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p1, p2, p3, p4, -, -, p5, p6, -⟩ := hP
    exact mul_pos (div_pos (mul_pos p3 p1) p5) (div_pos (mul_pos p4 p2) p6)
  have hκ : 0 < MassDataConc.kapN D := by
    have hg : (0 : ℝ) < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
      have h0 := (D.host.g_prime 0).pos
      have h1 := (D.host.g_prime 1).pos
      unfold Formalism.MainNotions.S.Lat.gS
      positivity
    have := rd_pos D
    unfold MassDataConc.kapN
    positivity
  have hIC : B.IntC = IntC X u u' 1 := by
    show IntC X u u' 1 / MassDataConc.kapN D * kapU D = _
    unfold kapU
    rw [if_pos hκ, div_mul_cancel₀ _ hκ.ne']
  rw [hIC] at hF1
  rw [hv] at hF2 hrdb
  have hrd := rd_pos D
  have hIre : 0 ≤ Ire := by
    have h0 : 0 ≤ (B.c0 * B.c0')⁻¹ * IntC X u u' 1 := mul_nonneg (inv_nonneg.2 hc0.le) ENNReal.toReal_nonneg
    rw [hF1, hF2, ← mul_assoc, ← kpl_pow] at h0
    exact nonneg_of_mul_nonneg_right h0 (pow_pos (kpl_pos D) _) |> fun h => h
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hrd1 : 1 ≤ D.host.rdE := hv ▸ LoopBCovN.rdE_ge_one D
  have he0 : 0 ≤ LoopBCovN.eN D := by unfold LoopBCovN.eN; positivity
  have hel := LoopBCovN.eN_le D
  refine ⟨hIre, 1, one_pos, LoopBTheta.normWin_one large₂ zero_le_one, fun Cc hB => ?_⟩
  have hLF := LocF.locFactor_holds hG Cc
  obtain ⟨νl, hpin, hQ⟩ := Formalism.L2.S.L6.UnitaryStandardVectors.ooQuot_of_nuQPin X u u' ν hp.2
  have hW : LoopTerm.CovWinN (Y := Y) Cc large₂ 1 u u' := by
    refine LoopBCovN.covWinN_of hF Cc large₂ zero_le_one ?_ u u'
    rw [hv]
    refine mul_le_mul (by nlinarith [sq_nonneg (D.R.m : ℝ)]) (Real.log_le_log hrd hrdb) (Real.log_nonneg hrd1)
      (by positivity)
  obtain ⟨hK0, hK1⟩ := AmpWinGlob.K0_mem_covWin_of_locFactor_wuBessel Cc u Y u' hLF hB (AmpWinJF.levelVolume_pos (X := X))
    (LoopBCovN.covN_pos hF one_pos Cc u u') hW
  refine ⟨⟨νl, hQ, hU D hG X 1 Cc hB u u' νl hpin⟩, hK0, hK1, fun sec hsec => ?_⟩
  rw [norm_eq Y Cc hB hLF u u' (hE D hG X u u') (c := B.c0) (c' := B.c0') rfl rfl hc0.ne' hF1 hF2 hsec]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hIre)
  rw [hF D X Y 1 Cc u one_pos, hF D X Y 1 Cc u' one_pos, one_mul, hv, D.what₂.card_Tau, ← pow_add, ← Real.rpow_natCast,
    ← Real.rpow_mul hrd.le]
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  refine (Real.rpow_le_rpow hrd.le hrdb (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hb1 ?_)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hel hf0]

end Formalism.MainStatements.RowRest
