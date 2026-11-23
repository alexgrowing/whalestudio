import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RelPtR
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PointUniformity
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RMeasP

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.BDatR Formalism.L2.SG.ThmBUseR
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowRestR {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ) ∧
    Formalism.L2.SG.Pf.JointAmplitudePoints.RMeasExP u u' C ∧ Formalism.L2.SG.Pf.JointAmplitudePoints.LocalAmplitudesPositive Y u u' ν C hB ∧
    Formalism.L2.SG.Pf.JointAmplitudePoints.ThetaWinP Y u u' ν C hB large₂ C1 ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

theorem rowBDataR_of_rest {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
    {ν : X.B.I.Ginf → Measure X.B.I.Ginf} {C1 Cn Ire : ℝ} (h : RowRestR large₂ Y u u' ν C1 Cn Ire) :
    RowBDataR large₂ Y u u' ν C1 Cn Ire := by
  obtain ⟨hI, θ, C, hB, hθ, hnw, hT, hM, hP, hTh, hN⟩ := h
  refine ⟨hI, θ, C, hB, hθ, hnw, hT, 1, zero_le_one, fun νL ng => ?_, fun sec hsec => ?_⟩
  · exact jointAmplitudeFactorizationRotated_of Y u u' large₂ C1 C hB ν νL ng (RelPtR.relPtExPR_holds C u u') hM hP hTh
  · rw [ENNReal.ofReal_one, one_mul]
    exact hN sec hsec

def RowRestUnifR : Prop :=
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
      ∀ ν, Pinned X u u' ν → RowRestR large₂ Y u u' ν C1 Cn Ire

theorem rowBDataUnifR_of (h : RowRestUnifR) : RowBDataUnifR := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, Cn, C'₀, Cl₀, hh⟩ := h Cg cb Cw cT CT C0
  refine ⟨C1, Cn, C'₀, Cl₀, ?_⟩
  intro C' Cl h1 h2 D large₂ X Y u u' hc hb X0 ψ ht sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hp
  exact rowBDataR_of_rest (hh C' Cl h1 h2 D large₂ X Y u u' hc hb X0 ψ ht sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hp)

theorem theoremB_fixed_final (hB : JointNormBoundRotatedUniform) (hA : AmpUnif) (hR : RowRestUnifR) : StepThmBPinnedC := by
  exact stepThmBPinnedC_ofR hB hA PointUniformity.ptUnif' (rowBDataUnifR_of hR)

theorem theoremB_uniform_rotated (h : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform) : JointNormBoundRotatedUniform := by
  exact h

theorem stepThmBPinnedC_of_exp (hE : Formalism.MainNotions.RotatedPoints.WeightedExpansionRotated) (hA : AmpUnif) (hR : RowRestUnifR) : StepThmBPinnedC := by
  exact theoremB_fixed_final (theoremB_uniform_rotated (Formalism.MainNotions.RotatedPoints.weighted_uniform_rotated_of_expansion hE)) hA hR

def AmplitudeMeasureBounds {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ) ∧
    Formalism.L2.SG.Pf.JointAmplitudePoints.LocalAmplitudesPositive Y u u' ν C hB ∧ Formalism.L2.SG.Pf.JointAmplitudePoints.ThetaWinP Y u u' ν C hB large₂ C1 ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

theorem rowRestR_of_2 {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
    {ν : X.B.I.Ginf → Measure X.B.I.Ginf} {C1 Cn Ire : ℝ} (h : AmplitudeMeasureBounds large₂ Y u u' ν C1 Cn Ire) :
    RowRestR large₂ Y u u' ν C1 Cn Ire := by
  obtain ⟨hI, θ, C, hB, hθ, hnw, hT, hP, hTh, hN⟩ := h
  refine ⟨hI, θ, C, hB, hθ, hnw, hT, RMeasP.rMeasExP_of_goodW C u u' (fun τ => ?_), hP, hTh, hN⟩
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hT τ
  exact goodW_of C u u' τ h1 h2 h3 h4 h5

def AmplitudeMeasureBoundsUniform : Prop :=
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
      ∀ ν, Pinned X u u' ν → AmplitudeMeasureBounds large₂ Y u u' ν C1 Cn Ire

theorem theoremB_fixed_of_expansion_measure (hE : Formalism.MainNotions.RotatedPoints.WeightedExpansionRotated) (hA : AmpUnif) (hR : AmplitudeMeasureBoundsUniform) :
    StepThmBPinnedC := by
  refine stepThmBPinnedC_of_exp hE hA ?_
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, Cn, C'₀, Cl₀, hh⟩ := hR Cg cb Cw cT CT C0
  refine ⟨C1, Cn, C'₀, Cl₀, ?_⟩
  intro C' Cl h1 h2 D large₂ X Y u u' hc hb X0 ψ ht sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hp
  exact rowRestR_of_2 (hh C' Cl h1 h2 D large₂ X Y u u' hc hb X0 ψ ht sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hp)

end Formalism.L2.SG.Pf.ThmBChain
