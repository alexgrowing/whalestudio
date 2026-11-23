import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXCovolPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.MassDataX

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc Formalism.L2.SG.Pf.MassDataPos Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DvPosC : Prop := ∀ {D : D7} (X : HidaSetting D) (v : NumberField.InfinitePlace X.B.I.F), 0 < X.dv v

theorem recPosC_of_dv {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hDv : DvPosC) (hX : HypX X hb FdN FdN' u u') :
    RecPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  have hTie := hX.1
  have hcol := (inColumnsAt_holds X hb hK FdN FdN' u u' X0 (Formalism.L2.SG.LocVol.locOf X u u' ψ)
    ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < Formalism.L2.SG.RealObj.degX X
    unfold Formalism.L2.SG.RealObj.degX
    exact Finset.prod_pos fun v _ => hDv X v
  · exact Nat.cast_pos.mpr (finrank_Vpi_pos X u)
  · exact Nat.cast_pos.mpr (finrank_Vpi_pos X u')
  · exact massH_pos X u
  · exact massH_pos X u'
  · show (0 : ℝ) < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d
    rw [show (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d = _ from hcol.1]
    exact mul_pos (Nat.cast_pos.mpr (finrank_Vpi_pos X u))
      (div_pos (covolH_pos X hb u hTie) (mul_pos (volH_pos X hb u hTie) (muHpp_pos X hb hK u)))
  · show (0 : ℝ) < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d'
    rw [show (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d' = _ from hcol.2.2.1]
    exact mul_pos (Nat.cast_pos.mpr (finrank_Vpi_pos X u'))
      (div_pos (covolH_pos X hb u' hTie) (mul_pos (volH_pos X hb u' hTie) (muHpp_pos X hb hK u')))

end Formalism.L2.SG.Pf.MassDataX

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.SpectralTiesReal
open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensNonnegAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (Lsp : LocSp D T.Y.M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]),
    0 ≤ supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p

theorem massDataPosAll_of (hP : ProdConvAll) (hSW : PI.VolStabS.MassDataS.SWXS) (hDv : Formalism.L2.SG.Pf.MassDataX.DvPosC)
    (hDN : DensNonnegAll) : MassDataPosAll := by
  intro D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hst hCT hdet hC hTh _
  have hK : T.X.LevelSubgroupNormalized := hCT.1
  have hV : 0 < T.X.volK2 := ENNReal.toReal_pos hK.2.2.1.ne' hK.2.2.2.ne
  have hX : Formalism.L2.SG.TypedSets.HypX T.X T.hb (T.Y.FN u) (T.Y.FN u') u u' :=
    ⟨T.measTie, hK, T.Y.FN_fund u, T.Y.FN_fund u'⟩
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of (hL := Formalism.L2.SG.Pf.MassDataX.locHaarPosC_holds ..)
    (hCv := Formalism.L2.SG.Pf.MassDataX.covolPosC_of (hSW := hSW) (hψ := T.ψ_char) (hC := T.measCompat)
      (hT := T.measTie) (hdet := hdet) ..)
    (hQv := Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of T.X T.hb T.Y u u' X0 T.ψ _ _ C Th _ Q _ _ i0 i0' νq hK hV)
    (hR := Formalism.L2.SG.Pf.MassDataX.recPosC_of_dv T.X T.hb T.Y.hK _ _ u u' X0 T.ψ _ _ C Th _ Q _ _ i0 i0' νq hDv hX)
    (hP := hP D T u u' hne hst) (hCoo := Formalism.L2.SG.Pf.MassDataPos.cooOf_pos T.X u u')
    (hκ := Formalism.L2.SG.WConst.kapN_pos) (hsd := hDN D T u u' Lsp ϖ) (hC := hC) (hTh := hTh) ..

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
