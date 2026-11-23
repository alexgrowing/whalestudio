import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRecPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassHNonneg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousSplitA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXColumns
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Volumes

namespace Formalism.L2.SG.Pf.MassDataX

theorem covolH_pos {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (hT : X.MeasTie hb) :
    0 < covol (X.measW w).μH := by
  have hM : massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X w) =
      covol (X.measW w).μH / ((X.muH w Set.univ).toReal *
        ((X.measW w).μHf (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal) :=
    MassDataMassesW.massAll_of hinfCompact_holds kCompactOpen_holds classFinite_holds X hb w hT
  have hm := massH_pos X w
  rw [hM] at hm
  rcases div_pos_iff.mp hm with h | h
  · exact h.1
  · exact absurd h.2 (not_lt.mpr (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))

theorem volH_pos {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (hT : X.MeasTie hb) :
    0 < (X.muH w Set.univ).toReal := by
  have hM : massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X w) =
      covol (X.measW w).μH / ((X.muH w Set.univ).toReal *
        ((X.measW w).μHf (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal) :=
    MassDataMassesW.massAll_of hinfCompact_holds kCompactOpen_holds classFinite_holds X hb w hT
  have hm := massH_pos X w
  rw [hM] at hm
  have h0 : (X.muH w Set.univ).toReal *
      ((X.measW w).μHf (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ≠ 0 := by
    intro h
    rw [h, div_zero] at hm
    exact lt_irrefl _ hm
  exact lt_of_le_of_ne ENNReal.toReal_nonneg (fun h => h0 (by rw [← h, zero_mul]))

theorem muHpp_pos {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) :
    0 < ((X.measW w).μHf (Subtype.val ⁻¹' K2u X hb w)).toReal := by
  haveI hHaar : (X.measW w).μHf.IsHaarMeasure := (X.measW_norm w).2.2.1
  obtain ⟨hO, h1, hsub⟩ := conjugated_level_open_one_mem (X := X) (hb := hb) (hK := hK) (u := w)
  have hHc := (closed_SNH_X (X := X) (u := w)).2.2
  have hKc := hHc.isClosedEmbedding_subtypeVal.isCompact_preimage (kCompactOpen_holds X).1
  have hKf : (X.measW w).μHf (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) < ⊤ := by
    exact hHaar.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact hKc
  have hfin : (X.measW w).μHf (Subtype.val ⁻¹' K2u X hb w) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.preimage_mono hsub)) hKf
  have hpos : (X.measW w).μHf (Subtype.val ⁻¹' K2u X hb w) ≠ 0 :=
    ((hO.preimage continuous_subtype_val).measure_pos _ ⟨1, h1⟩).ne'
  exact ENNReal.toReal_pos hpos hfin.ne

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc Formalism.L2.SG.Pf.MassDataPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem covolPosC_of (hSW : PI.VolStabS.MassDataS.SWXS) (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ)
    (hT : X.MeasTie hb) (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) :
    CovolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  have hs := MassDataVolumesW.stepSizeW X
  have hH := covolH_pos X hb u hT
  have hH' := covolH_pos X hb u' hT
  have hG : 0 < covolBy (G := HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
      X.measG.μG := by
    rw [← covolH_eq_volG hSW X ψ hψ hC u]; exact hH
  obtain ⟨hTB, νB, hνB, hcB⟩ := hC.2 X0 hdet
  have eB := MassDataVolumesW.covol_eq_covolBy_w (PI.VolStabS.MassDataS.volStabXS_of hSW X) (MassDataVolumesW.stepHerm X)
    (a := 2 * D.R.rS + 2) (by omega) (by omega) X0 hTB hdet hψ X.measG_norm.1 hνB (X.measG_norm.2.2.2.2.1 X0) hcB
  refine ⟨hG, hH, hH', ?_, ?_, ?_⟩
  · show 0 < covol (X.measW u).μN
    rw [(hC.1 u).2]; exact one_pos
  · show 0 < covol (X.measW u').μN
    rw [(hC.1 u').2]; exact one_pos
  · show 0 < covol (X.measG.μB X0)
    rw [eB]; exact hG

end Main

end Formalism.L2.SG.Pf.MassDataX
