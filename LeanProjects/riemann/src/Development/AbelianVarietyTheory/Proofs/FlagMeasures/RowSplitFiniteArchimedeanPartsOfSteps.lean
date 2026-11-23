import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  GlobalTheory.NGRow

namespace GlobalTheory.NGRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ngCut2P_of_steps (hM : StepAnalyticConstantsP) (hS : StepSizes) (hC : StepClass) (hN : StepNormals)
    (hP : StepPoints) (hH : StepHeight) : NGCut2P := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hM Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩ := hA1 (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩ := hS Cg cb Cw cT CT C0
  obtain ⟨n₀, m₀, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨p₀, q₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨h₀, j₀, hH2⟩ := hH Cg cb Cw cT CT C0
  refine ⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _,
    max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))),
    fun C' Cl h1 h2 D large₂ X Y u u' hTies h0 hs hT => ?_⟩
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' := ⟨h0, hs, hT⟩
  have e1' : a₀ ≤ C' := le_trans (by simp) h1
  have e2' : b₀ ≤ Cl := le_trans (by simp) h2
  have f1 : s₀ ≤ C' := le_trans (by simp) h1
  have f2 : t₀ ≤ Cl := le_trans (by simp) h2
  have i1 : n₀ ≤ C' := le_trans (by simp) h1
  have i2 : m₀ ≤ Cl := le_trans (by simp) h2
  have j1 : p₀ ≤ C' := le_trans (by simp) h1
  have j2 : q₀ ≤ Cl := le_trans (by simp) h2
  have k1 : h₀ ≤ C' := le_trans (by simp) h1
  have k2 : j₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨P, iP, B, Irat, Ire, hBk, νL, νB, ng, cSt, e1, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩ :=
    hA2 C' Cl e1' e2' D large₂ X Y u u' hTies hc
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk
  refine ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI,
    ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u' hc) c1 c2 c3 c4, ?_, hMeas, hSum⟩
  exact ⟨hC D X Y u u' hT νL νB ng, ampInput_of_vanish Y u u' νL νB ng hV,
    hN2 C' Cl i1 i2 D large₂ X Y u u' hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u u' hc νL νB ng, hLoc, hGen,
    hH2 C' Cl k1 k2 D large₂ X Y u u' hc νL νB ng⟩

end GlobalTheory.NGRow
