import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocMassTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSDLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmegaUnramifiedHolds

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

def SDLocX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), IsSDLoc X.B.I.cm.sig X.B.I.J v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def UnramTypX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), TypAt X v → UnramAt (E := X.B.I.E) v

def STypIdx : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X), X.MeasTie hb →
    ((X.measW u).μSv p.1).IsHaarMeasure →
    ((X.measW u).μSv p.1 (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1)).toReal =
      ((glkC D.R.k (gOf p) : ℕ) : ℝ) / ((ukC D.R.k (gOf p) : ℕ) : ℝ) *
        ((X.measW u).μSv p.1 (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1)).toReal

theorem gAt_mem {D : D7} (X : HidaSetting D) (p : TypX X) : ((gAt X p.1 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  obtain ⟨p, hp⟩ := p
  have hT : IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) p := by
    unfold typSet at hp
    split_ifs at hp with hfin
    · simpa using hp
    · simp at hp
  unfold gAt
  split_ifs with h0
  · exact h0
  · unfold IsTyped at hT
    exact hT.resolve_left h0

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc

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

theorem inTypedC_loc (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) (hψ : IsCharAF X.B.I.F ψ) (hψs : IsStdChar ψ) :
    InTypedC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro hX _hP hL hL' hTF p
  have hlat : ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E), Submodule.IsLattice X.B.I.E L ∧
      (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    ⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩
  have hTyp : TypAt X p.1 := p.2
  refine ⟨?_, hI X hb u p hX.1 (hL p.1).2.1, hI X hb u' p hX.1 (hL' p.1).2.1⟩
  have h := locMassTyp X.B.I.cm.sig X.B.I.J ψ p.1 (gAt X p.1) (frameOf X u) (frameOf X u')
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hψ, hψs⟩ _ _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u) (MassDataLevelSSteps.FrameW.frameOf_isStd X u')
    (hSD X p.1) (hUn X p.1 hTyp) hlat (hTF p).1 (gAt_mem X p) (hTF p).2.1 (hTF p).2.2.1 (hTF p).2.2.2.2
    _ (hL p.1).1 _ (hL p.1).2.1 (hL p.1).2.2.1 _ (hL' p.1).2.1 (hL' p.1).2.2.1 (hL p.1).2.2.2 (hL' p.1).2.2.2
  show MX X u u' ψ p.1 / localVolumeUnit X ψ p.1 = _
  unfold MX localVolumeUnit OmX
  rw [if_pos hTyp, if_pos hTyp]
  exact h

theorem typedAll_of (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  exact inTypedC_loc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSD hUn hI T.ψ_char T.ψ_std

theorem typedAll_of_idx (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll :=
  typedAll_of (fun X v => Formalism.L2.SG.Pf.MassDataX.SDL.sdLocX_holds X v)
    (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) hI

end Main

end Formalism.L2.SG.Pf.MassDataX
