import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamNG

theorem ampQ_id {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ id L = L.ampNG := by
  funext d
  unfold ampQ PN.LocalNG.ampNG
  simp only [id]

theorem hasPt_of_isPt {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
    {νL νB : X.B.I.Ginf → Measure X.B.I.Ginf} {ng : PN.Pts D.host.E D.R.rS → ℝ} {γ : PN.Pts D.host.E D.R.rS}
    (h : PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ) : HasPt Y u u' (Y.tO u u').ngSet γ := by
  obtain ⟨-, -, t, ht, hv, -, hp, -⟩ := h
  exact ⟨t, ht, hv, hp⟩

theorem leaves_of_fam : FamNG → (FamilyWeightSumUnfoldingIdentity → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) ∧ (WeightsFam → Formalism.L2.SG.FamDefs.WeightsNG) ∧
    (FamilyGroupSumFactorsWeightAmplitude → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) ∧ (ExistFam → Formalism.L2.SG.FamDefs.ExistNG) := by
  intro hF
  refine ⟨fun hG => ?_, fun hW => ?_, fun hG4 => ?_, fun hE => ?_⟩
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hG Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S Fm hT => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ
      (hasPt_of_isPt hγ) Fm hT
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hW Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire
      hbk νL νB ng γ hγ S Fm hT hRel hTerm hG5 => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q
      i0 i0' νq Irat Ire hbk _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT hRel hTerm hG5
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨CSt, hCSt, a2, b2, h2⟩ := hG4 Cg cb Cw cT CT C0
    refine ⟨CSt, hCSt, max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0'
      νq Irat Ire hbk ν hν => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0
      ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hν
    refine ⟨s, hs1, hs2, hs3, fun γ hγ S Fm hT x _ => ?_⟩
    have h := hs4 _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT x.1 x.2
    rw [ampQ_id] at h
    exact h
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hE Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ (hasPt_of_isPt hγ)

end GlobalTheory.SnFamNG
