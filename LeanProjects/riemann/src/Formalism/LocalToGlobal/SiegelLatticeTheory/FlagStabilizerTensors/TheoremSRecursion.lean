import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarDisintegrationRealHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcTieCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolKap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolPrim

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.SpectralTiesReal

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

def KernelExponentAgreement : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    Formalism.L2.SG.TermOp.KExpansion (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u) (Y.Dt u')

def FinXC : Prop := ∀ (D : D7) (T : STies D), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → FinX T.Y

def FormulaC : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (Lsp : LocSp D T.Y.M), Formalism.L2.SG.Pf.LocCP.LocTied D →
    Formalism.MainNotions.S.Cnt.Stand D u u' → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    Formula T.Y.δ Lsp u u' (T.X.Fu u) (T.Y.what₂ u) (Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u))

def ChoicesC : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word), u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' →
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k →
    ∃ (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (Lsp : LocSp D T.Y.M)
      (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (κ : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℕ)
      (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u)),
      (∀ v, i0 v = i0' v) ∧ PtRepExists T.X u u' 1 i0 i0' ∧ NuQPin T.X u u' νq ∧
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE T.X.B.I.cm.sig T.X.B.I.J X0).det ≠ 0 ∧ (∀ p, Irreducible (ϖ p)) ∧ RowLabel κ

def RowsSumC : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
    (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) (Lsp : LocSp D T.Y.M)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℕ),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (∀ i, 3 ≤ D.host.g i) → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k →
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq → RowLabel κ →
    RowsSum (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) κ
      (Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u) * ∏' p, alpD u u' p)
      (VtPt T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq)

def RowFormAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E)
    (C Th : ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) (Lsp : LocSp D T.Y.M)
    (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (κ : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℕ),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (∀ i, 3 ≤ D.host.g i) → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE T.X.B.I.cm.sig T.X.B.I.J X0).det ≠ 0 →
    2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
    RowLabel κ → (∀ p, Irreducible (ϖ p)) →
    Formalism.L2.SG.MassDataForm.RowFormC T.X T.hb T.Y u u' X0 T.ψ
      (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq κ
      (Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u))

def MassDataHypAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (C Th : ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) (Lsp : LocSp D T.Y.M)
    (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ConcTie T.X T.Y → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE T.X.B.I.cm.sig T.X.B.I.J X0).det ≠ 0 → 0 ≤ C → 0 < Th →
    2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq → (∀ p, Irreducible (ϖ p)) →
    PB.MassDataHyp (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq)

def LinkAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (τ : D.what₂.Tau)
    (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (C Th : ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) (Lsp : LocSp D T.Y.M)
    (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE T.X.B.I.cm.sig T.X.B.I.J X0).det ≠ 0 →
    ((gOf D e).size (deOf D τ u) (D.mem u).A.T (D.duS u)).Dstar = D.what₂.Dstar →
    PB.Link (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq)
      (gOf D e) (deOf D τ u) (D.mem u).A.T (D.duS u) (D.duS u')

def SplitAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (C Th : ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) (Lsp : LocSp D T.Y.M)
    (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (∀ i, 3 ≤ D.host.g i) →
    PB.SplitInputs (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq).tt

def CardC : Prop := ∀ (D : D7) (T : STies D), Fintype.card (InfinitePlace T.X.B.I.F) = D.R.f

theorem cardC_holds : CardC := by
  intro D T
  rw [Fintype.card_congr T.X.pl]
  exact D.what₂.card_Tau

def SizesAt (CA C0 CG CDel cT Cb Cn : ℝ) (k0 : ℕ) (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) : Prop :=
  ∃ (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (τ : D.what₂.Tau) (Cp Th Cf : ℝ),
    (∀ x : InfinitePlace D.host.E,
      InfinitePlace.mk ((T.X.B.I.φ (T.X.pl.symm (e x))).comp T.X.ιE.symm.toRingHom) = x) ∧
    k0 ≤ (gOf D e).k ∧
    J.SzHyp (gOf D e) CA C0 CG CDel cT Cb L.sc.b Cp Th (deOf D τ u) (deOf D τ u') (D.mem u).A.T (D.mem u').A.T
      (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) ∧
    16 ≤ Sz.cExp CDel cT Cb * Cf ∧ Cf * Real.log L.sc.b ≤ (gOf D e).f * Real.log (gOf D e).k ∧
    2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k ∧
    PB.SizeNumbers (gOf D e).k (gOf D e).r (gOf D e).f L.sc.b (gOf D e).g1 (gOf D e).g2 (1 / 3) Cn ∧
    ((gOf D e).size (deOf D τ u) (D.mem u).A.T (D.duS u)).Dstar = D.what₂.Dstar ∧
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2]

section MassDataLeaves

open Formalism.L2.SG.TypedSets Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol

def MassDataPosAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (C Th : ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) (Lsp : LocSp D T.Y.M)
    (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE T.X.B.I.cm.sig T.X.B.I.J X0).det ≠ 0 → 0 ≤ C → 0 < Th →
    (∀ p, Irreducible (ϖ p)) →
    MassDataPosY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq

def MassDataVolAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd C Th : ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
    InVolumesAt T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 (locOf T.X u u' T.ψ)
        (anY T.X T.Y u u' T.ψ sd C Th (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq) ∧
      InLevelSAt T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 (locOf T.X u u' T.ψ)
        (anY T.X T.Y u u' T.ψ sd C Th (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq) ∧
      InMassesAt T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 (locOf T.X u u' T.ψ)
        (anY T.X T.Y u u' T.ψ sd C Th (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq) ∧
      InColumnsAt T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 (locOf T.X u u' T.ψ)
        (anY T.X T.Y u u' T.ψ sd C Th (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq) ∧
      InIndicesAt T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 (locOf T.X u u' T.ψ)
        (anY T.X T.Y u u' T.ψ sd C Th (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq)

def ProdConvAll : Prop := ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word), u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ProdConv T.X u u' T.ψ

def TypedAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd C Th : ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
    InTypedC T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u') sd C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq

def GSplitAll : Prop := ∀ (D : D7) (T : STies D), GSplitX T.X

theorem gSplitAll_holds : GSplitAll := fun _ T => Formalism.L2.SG.Pf.gSplitX_holds T.X

theorem massDataInputsAll_of (hPos : MassDataPosAll) (hV : MassDataVolAll) (hP : ProdConvAll) (hTy : TypedAll)
    (hInf : ∀ D : D7, Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word), InInfinityX X u u' 1)
    (hPrim : _root_.PI.LocFramePrim.Statement) : MassDataHypAll := by
  intro D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hGap hCT hdet hC hTh _ _ hii hPt hNu hϖ
  have hPs := hPos D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hdet hC hTh hϖ
  have hH : HypX T.X T.hb (T.Y.FN u) (T.Y.FN u') u u' := ⟨T.measTie, hCT.1, T.Y.FN_fund u, T.Y.FN_fund u'⟩
  obtain ⟨hVo, hLS, hMs, hCo, hIx⟩ := hV D T u u' X0 (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p)
    C Th Q i0 i0' νq
  exact massDataInputs_Y T.X T.hb T.Y u u' X0 T.ψ _ C Th _ Q i0 i0' νq hPs
    (inFormC_bCF T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u') _ C Th _ Q T.Y.M T.Y.δ i0 i0' νq
      (ne_of_gt (pos_rho hPs)))
    (Formalism.L2.SG.Pf.realObj_inNuX T.X u u' 1) (hInf D hGap T.X u u')
    (Formalism.L2.SG.Pf.NcAsm.kapN_ne D) hH
    hVo T.ψ_char T.ψ_std T.measCompat hdet hLS hMs hCo hIx (hP D T u u' hne hSt) (hTy D T u u' X0 _ C Th Q i0 i0' νq)
    (locTieX_of T.X T.ψ u (T.locCompat u) (Formalism.L2.SG.Pf.LocVolPrim.primX T.X u hPrim))
    (locTieX_of T.X T.ψ u' (T.locCompat u') (Formalism.L2.SG.Pf.LocVolPrim.primX T.X u' hPrim))
    (typFacts_of T.X u u' (gSplitAll_holds D T) (tCongX T.X u u') (Formalism.L2.SG.LocVolKap.kapX T.X T.hb u u'))

end MassDataLeaves

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
