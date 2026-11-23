import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocNorm

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.ThmBChain Formalism.L2.SG.Pf.OOCore3 Formalism.L2.SG.Pf.LocNorm
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChain5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AmplitudeBoundsForChoice {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ) ∧
    (∃ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl ∧ LocUniqP u u' C hB νl ∧ MeasP u u' C hB νl) ∧
    0 < K0 Y u u' C hB ∧ WinK large₂ C1 (K0 Y u u' C hB) ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

theorem remainingFactsLocal_of_choice {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
    {ν : X.B.I.Ginf → Measure X.B.I.Ginf} {C1 Cn Ire : ℝ} (h : AmplitudeBoundsForChoice large₂ Y u u' ν C1 Cn Ire) :
    LocalAmplitudeBounds large₂ Y u u' ν C1 Cn Ire := by
  obtain ⟨hIre, θ, C, hB, h0, hw, hl, ⟨νl, hQ, hU, hM⟩, hK, hW, hN⟩ := h
  exact ⟨hIre, θ, C, hB, h0, hw, hl, ⟨νl, hQ, locNormPK_of Y u u' C hB large₂ C1 νl hU hM hK hW⟩, hN⟩

def AmplitudeBoundsForChoiceUniform : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → AmplitudeBoundsForChoice large₂ Y u u' ν C1 Cn Ire

theorem theoremB_fixed_of_choice (hE : Formalism.MainNotions.RotatedPoints.WeightedExpansionRotated) (hA : AmpUnif) (hR : AmplitudeBoundsForChoiceUniform) :
    StepThmBPinnedC := by
  refine Formalism.L2.SG.Pf.OOCore3.theoremB_fixed_of_expansion_lemmaJ hE hA fun Cg cb Cw cT CT C0 => ?_
  obtain ⟨C1, Cn, a, b, h2⟩ := hR Cg cb Cw cT CT C0
  exact ⟨C1, Cn, a, b, fun C' Cl h1 h3 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp =>
    remainingFactsLocal_of_choice (h2 C' Cl h1 h3 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp)⟩

end Formalism.L2.SG.Pf.ThmBChain5
