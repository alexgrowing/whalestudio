import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTied
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataVolumesS
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataLevelS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXMasses

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Clauses

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem inMass_bCF : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass :=
  inMass_bC X hb hK FdN FdN' u u' X0 _ T sd C Th _ (massH_pos X u).ne'

theorem inMasses_bCF (hX : HypX X hb FdN FdN' u u') :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses := by
  have h := inMassesAt_holds X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX
  exact h

theorem inLevelS_bCF (hX : HypX X hb FdN FdN' u u') :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS := by
  have h := level_s_at_instance X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX
  exact h

theorem inVolumes_bCF (hSW : PI.VolStabS.MassDataS.SWXS) (hX : HypX X hb FdN FdN' u u') (hψ : IsCharAF X.B.I.F ψ)
    (hstd : IsStdChar ψ) (hC : MeasCompatψ X ψ) (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes := by
  have h := inVolumes_of_compat X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    (volumes_s_at_instance hSW X hb hK FdN FdN' u u' X0 _ _) hX ⟨ψ, hψ, hstd, hC⟩ hdet
  exact h

theorem inTyped_bCF (hX : HypX X hb FdN FdN' u u') (hP : ProdConv X u u' ψ) (hL : LocTieX X ψ u) (hL' : LocTieX X ψ u')
    (hTF : TypFacts X u u') (hψ : IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped :=
  inTypedC_loc X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (fun X v => SDL.sdLocX_holds X v) (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) sTypIdx_holds
    hψ hstd hX hP hL hL' hTF

theorem pos_bCF (hSW : PI.VolStabS.MassDataS.SWXS) (hX : HypX X hb FdN FdN' u u') (hP : ProdConv X u u' ψ)
    (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ) (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0)
    (hQ : Formalism.L2.SG.Pf.MassDataPos.QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hsd : 0 ≤ sd) (hC0 : 0 ≤ C) (hTh : 0 < Th) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos := by
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (locHaarPosC_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (covolPosC_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hψ hC hX.1 hdet)
    hQ
    (recPosC_of_dv X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (fun X v => dvPosC_holds X v) hX)
    hP (Formalism.L2.SG.Pf.MassDataPos.cooOf_pos X u u') (Formalism.L2.SG.WConst.kapN_pos (D := D)) hsd hC0 hTh

end Clauses

end Formalism.L2.SG.Pf.MassDataX
