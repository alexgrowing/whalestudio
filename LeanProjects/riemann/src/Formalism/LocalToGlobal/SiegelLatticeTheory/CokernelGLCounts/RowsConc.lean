import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsOther
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt

set_option linter.dupNamespace false

namespace Formalism.L2.SG.RowsConc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Num

variable {D : D7} (X : HidaSetting D) (Y : Full X)

def duC (u : D.what₂.Word) : ℝ := (Module.finrank ℂ (Cu X u Y.hK) : ℝ)

def DstC : ℝ := X.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll X.B.I X.B.σ X.B.w) X.B.μf X.B.fund X.B.e

def ddC (u u' : D.what₂.Word) : ℝ := duC X Y u * duC X Y u' / DstC X

def oneC (u : D.what₂.Word) : Formalism.L2.SG.PackageTie.HS (CM (Y.cs u)) (CM (Y.cs u)) :=
  Formalism.L2.SG.PackageTie.hsEmb (ContinuousLinearMap.id ℂ (CM (Y.cs u)))

end Num

def PgC {D : D7} {X : HidaSetting D} (Y : Full X) : ℝ := ∏ v, (1 + 3 / (Fintype.card (Y.TR.Fq v) : ℝ))

def mR (D : D7) : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ)

def epsL (D : D7) : ℝ := Real.exp (-((1 / 3 : ℝ) * D.R.k * D.R.f * Real.log D.R.k))

def epsK (D : D7) : ℝ := Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

def epsNG (D : D7) (large₂ : SizeData₂ D) (C4 : ℝ) : ℝ :=
  ((2 : ℝ) ^ (D.R.k - 2 * D.R.rS - 5))⁻¹ * Real.exp (C4 * mR D ^ 5 * D.R.f * Real.log large₂.sc.b)

def gamB (D : D7) (large₂ : SizeData₂ D) (CB : ℝ) : ℝ := Real.exp (CB * mR D ^ 5 * D.R.f * Real.log large₂.sc.b)

def TFrameAt (D : D7) : Prop :=
  ∀ w : D.what₂.Word, 1 ≤ Formalism.MainNotions.S.Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS)

def ConcTie {D : D7} (X : HidaSetting D) (Y : Full X) : Prop :=
  X.LevelSubgroupNormalized ∧ (∀ u, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) ∧ (∀ u, duC X Y u = (D.duS u : ℝ)) ∧ DstC X = D.what₂.Dstar ∧
    Formalism.L2.SG.WuDecay.WuDecay X ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    (∃ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
      X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧
      Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Formalism.L2.SG.Pf.LocCP.LocTied D) ∧
    TFrameAt D

section Closed

def KppOffC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → u ≠ u' →
      Formalism.L2.SG.RowsOther.KppTermZero (Y.tO u u')

def KppDiagC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      Summable ((Y.tO u u).degSet.indicator (fun t => ‖(Y.tO u u).op t‖)) ∧
      Formalism.L2.SG.RowsOther.KppDiag (Y.tO u u) (duC X Y u) D.R.k D.R.f

def RowLoopsC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u').AbsConv →
      (Y.tO u u').RowBig (epsL D) (ddC X Y u u') ∧ (Y.tO u u').RowNotScalar (epsL D) (ddC X Y u u')

def RowNGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C4 : ℝ, 0 ≤ C4 ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie X Y → (Y.tO u u').AbsConv →
      (Y.tO u u').RowNG (epsNG D large₂ C4) (ddC X Y u u')

def RowMainEqC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).RowMain (gamB D large₂ CB) (ddC X Y u u)

def DiagC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ CB C4 : ℝ, 0 ≤ CB ∧ 0 ≤ C4 ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT → ConcTie X Y →
      (Y.tO u u).AbsConv → max CB C4 + 1 ≤ large₂.CGam →
      Formalism.L2.SG.RowsOther.DiagRow (Y.tO u u) (oneC X Y u) (D.mem u).A.GamP (ddC X Y u u)

end Closed

section Facts

variable {D : D7} {X : HidaSetting D} {Y : Full X}

theorem dst_pos (h : ConcTie X Y) (u : D.what₂.Word) : 0 < DstC X := by
  rw [h.2.2.2.1, ← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos

theorem dd_nonneg (h : ConcTie X Y) (u u' : D.what₂.Word) : 0 ≤ ddC X Y u u' := by
  unfold ddC
  have h1 : 0 ≤ duC X Y u := Nat.cast_nonneg _
  have h2 : 0 ≤ duC X Y u' := Nat.cast_nonneg _
  exact div_nonneg (mul_nonneg h1 h2) (dst_pos h u).le

theorem cu_fd (h : ConcTie X Y) (u : D.what₂.Word) (hC : Formalism.L2.SG.PoincareInHH.Cut.ClassFin X u Y.hK) :
    FiniteDimensional ℂ (Cu X u Y.hK) :=
  (Formalism.L2.SG.PoincareInHH.Cut.cols_dim_of_neat X u Y.hK (h.2.1 u) hC).1

end Facts

section Cut

def AbsConvTied : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → (Y.tO u u').AbsConv

def NormExpSatTied : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    (Y.tO u u').NormExpansionOn (Y.tO u u').genSet ∧ (Y.tO u u').NormExpansionOn (Y.tO u u').ngSet

def NormExpDegC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    (Y.tO u u).NormExpansionOn (Y.tO u u).degSet

def CorankPosC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → (Y.tO u u').CorankPos

def IdOneC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    Formalism.L2.SG.RowsOther.IdOne (Y.tO u u) (oneC X Y u)

theorem card_ge_three {D : D7} {large₂ : SizeData₂ D} {Cl Cg CT : ℝ} (hK : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT)
    {X : HidaSetting D} (TR : TypedRed X) (v : TR.Pl) : 3 ≤ Fintype.card (TR.Fq v) := by
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb : 1 < large₂.sc.b := by
    unfold Formalism.BasicNotions.Scale.b
    have := Real.add_one_lt_exp (ne_of_gt hL); linarith
  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hkb : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have h8 : (3 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hkb 8)
  rcases TR.card_q v with h | h
  · rw [h]; exact_mod_cast h8.trans (hK.2.1 0).1
  · rw [h]; exact_mod_cast h8.trans (hK.2.1 1).1

def LoopsCutC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∀ K₀ : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y →
      ∃ (Al NT Gam : ℝ) (Xi : ℕ → ℝ), 1 ≤ Al ∧
        Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v NT Gam ∧
        Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v NT Xi ∧
        6 * Real.log (3 * Al) ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k ∧
        Formalism.L2.SG.RowsOther.LoopsAmp (Y.tO u u') Al C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v Gam Xi
          (ddC X Y u u')

theorem rowLoopsC_of_cut (hL : PN.LoopCores) (hSub : PB.SubFamily) (hc : LoopsCutC) :
    RowLoopsC := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨C, hC, hK⟩ := hc Cg cb Cw cT CT C0 A
  obtain ⟨K₀, hJ⟩ := Formalism.L2.SG.RowsOther.rowLoops_of_input hL hSub C hC
  obtain ⟨C'₀, Cl₀, h⟩ := hK K₀
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u u' hH hT ha => ?_⟩
  obtain ⟨Al, NT, Gam, Xi, hA1, hP, hX, h6, hAmp⟩ := h C' Cl h1 h2 D large₂ X Y u u' hH hT
  exact hJ _ _ _ _ _ (Y.tO u u') D.R.k D.R.rS D.R.f Al large₂.sc.b (X.B.g : ℝ) D.host.v NT Gam Xi (ddC X Y u u')
    hA1 hP hX h6 (dd_nonneg hT u u') ha
    (Formalism.L2.SG.RowsOther.loopsInput_of_amp _ ha.2.2.le _ _ _ _ _ _ _ _ _ _ _ hAmp)

def PairsDegCutC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y →
      Formalism.L2.SG.RowsOther.PairsDegAmp (Y.tO u u) (PgC Y) (duC X Y u) D.R.k D.R.f

theorem kppDiagC_of_cut (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit) (hSub : PB.SubFamily)
    (hGG : Formalism.L2.SG.GGMirabolic.TermsGGBound) (hC : CorankPosC) (hN : NormExpDegC)
    (hc : PairsDegCutC) : KppDiagC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hH hT ha => ?_⟩
  have hG0 : 0 ≤ (Y.tO u u).Gam1 := ha.2.2.le
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hGB : (Y.tO u u).GGBound (PgC Y) :=
    Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) hGG Y.psi_ne
      (fun v => card_ge_three hH.2 Y.TR v)
  refine ⟨ha.1.indicator _, ?_⟩
  exact Formalism.L2.SG.RowsOther.kppDiag_of_pairs (Y.tO u u) hP hE hS hSub (PgC Y) (duC X Y u) D.R.k D.R.f hPg ha
    (Formalism.L2.SG.TermOp.rowOrth Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u)) (hC D X Y u u hT) (hN D X Y u hT) hGB
    (Formalism.L2.SG.RowsOther.pairsDeg_of_amp _ hG0 _ _ _ _ hPg (h C' Cl h1 h2 D large₂ X Y u hH hT))

def DiagNumC : Prop :=
  ∀ Cg cb Cw cT CT C0 A CB C4 : ℝ, 0 ≤ CB → 0 ≤ C4 → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT → ConcTie X Y →
      max CB C4 + 1 ≤ large₂.CGam →
      (√(PgC Y * (gamB D large₂ CB + 2 * epsL D)) + √(PgC Y * (epsL D + epsNG D large₂ C4))) ^ 2 ≤ (D.mem u).A.GamP

theorem diagC_of_rows (hA : PB.PairBoundAbstract) (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit)
    (hSub : PB.SubFamily) (hGG : Formalism.L2.SG.GGMirabolic.TermsGGBound)
    (hNS : NormExpSatTied) (hC : CorankPosC) (hId : IdOneC) (hL : RowLoopsC) (hNG : RowNGC) (hM : RowMainEqC)
    (hNum : DiagNumC) : DiagC := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨CB, hCB, C'₁, Cl₁, hM'⟩ := hM Cg cb Cw cT CT C0 A
  obtain ⟨C4, hC4, C'₂, Cl₂, hNG'⟩ := hNG Cg cb Cw cT CT C0
  obtain ⟨C'₃, Cl₃, hL'⟩ := hL Cg cb Cw cT CT C0 A
  obtain ⟨C'₄, Cl₄, hNum'⟩ := hNum Cg cb Cw cT CT C0 A CB C4 hCB hC4
  refine ⟨CB, C4, hCB, hC4, max (max C'₁ C'₂) (max C'₃ C'₄), max (max Cl₁ Cl₂) (max Cl₃ Cl₄),
    fun C' Cl h1 h2 D large₂ X Y u hH hK2 hT ha hG => ?_⟩
  have a1 : C'₁ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
  have a2 : C'₂ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1
  have a3 : C'₃ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1
  have a4 : C'₄ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h1
  have b1 : Cl₁ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h2
  have b2 : Cl₂ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
  have b3 : Cl₃ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h2
  have b4 : Cl₄ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h2
  have h0 : Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 := hH.1
  have hs : Formalism.MainNotions.S.Cnt.Stand D u u := hH.2.1
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdd := dd_nonneg hT u u
  obtain ⟨r1, r2⟩ := hL' C' Cl a3 b3 D large₂ X Y u u hH hT ha
  have r3 := hM' C' Cl a1 b1 D large₂ X Y u hH hT ha
  have r4 := hNG' C' Cl a2 b2 D large₂ X Y u u h0 hs hT ha
  have hGB : (Y.tO u u).GGBound (PgC Y) :=
    Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) hGG Y.psi_ne
      (fun v => card_ge_three hK2 Y.TR v)
  have hD := Formalism.L2.SG.RowsOther.diag_of_abstract (Y.tO u u) hA hP hE hS hSub (oneC X Y u) (PgC Y)
    (gamB D large₂ CB) (epsL D) (epsNG D large₂ C4) (ddC X Y u u) hPg hdd ha (hNS D X Y u u hT) hGB
    (Formalism.L2.SG.TermOp.rowOrth Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u)) (hC D X Y u u hT) (hId D X Y u hT)
    r1 r2 r3 r4
  unfold Formalism.L2.SG.RowsOther.DiagRow at hD ⊢
  exact hD.trans (mul_le_mul_of_nonneg_right (hNum' C' Cl a4 b4 D large₂ X Y u hH hK2 hT hG) hdd)

end Cut

section FromFull

open Formalism.L2.SG.WuDecay

theorem absConvTied_of_full (hFo : FoldOKC) (hF : FundExistsC) (hO : OOIntAllC)
    (hA : AbsConvC) : AbsConvTied := by
  intro D X Y u u' hT
  have f1 := hFo D X Y u hT.1 hT.2.2.2.2.1
  have f2 := hFo D X Y u' hT.1 hT.2.2.2.2.1
  exact hA D X Y u u' f1 f2 (hF D X Y u u') (hO D X Y u u' f1 f2 (hF D X Y u u'))

theorem normExpSatTied_of_full (hFo : FoldOKC) (hF : FundExistsC) (hO : OOIntAllC)
    (hA : AbsConvC) (hAW : AmpWellDefC) (hCh : ChiNIndepC) (hN : NormExpSatC) : NormExpSatTied := by
  intro D X Y u u' hT
  have f1 := hFo D X Y u hT.1 hT.2.2.2.2.1
  have f2 := hFo D X Y u' hT.1 hT.2.2.2.2.1
  have hOO := hO D X Y u u' f1 f2 (hF D X Y u u')
  exact hN D X Y u u' (hAW D X Y u u' hOO) (hCh D X Y u u') (absConvTied_of_full hFo hF hO hA D X Y u u' hT)

theorem hasSum_hsEmb {ι : Type*} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {f : ι → W →L[ℂ] W} {a : W →L[ℂ] W} (h : HasSum f a) :
    HasSum (fun i => Formalism.L2.SG.PackageTie.hsEmb (f i)) (Formalism.L2.SG.PackageTie.hsEmb a) :=
  h.map (Formalism.L2.SG.PackageTie.hsEmb (Wq := W) (Wp := W)) (LinearMap.continuous_of_finiteDimensional _)

theorem idOne_of_cell {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (h : Formalism.L2.SG.TermOp.IdCellDiag (X.Fu u) (Y.cs u) (Y.FN u)) :
    Formalism.L2.SG.RowsOther.IdOne (Y.tO u u) (oneC X Y u) := by
  have hs := hasSum_hsEmb (h (Y.FN_fund u))
  unfold Formalism.L2.SG.RowsOther.IdOne PB.Terms.part
  rw [← tsum_subtype]
  exact hs.tsum_eq

theorem idOneC_of_full (hFo : FoldOKC) (hF : FundExistsC) (hO : OOIntAllC)
    (hI : IdCellDiagC) : IdOneC := by
  intro D X Y u hT
  have f1 := hFo D X Y u hT.1 hT.2.2.2.2.1
  exact idOne_of_cell Y u (hI D X Y u hT.1 (hF D X Y u u) (hO D X Y u u f1 f1 (hF D X Y u u)))

theorem norm_vec {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    ‖(Y.tO u u').vec t‖ =
      wt t * ‖Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t)‖ := by
  show ‖vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t‖ = _
  unfold vec
  have e : (fun q : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u'} => if q = (⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩) then
      ((wt t : ℝ) : ℂ) • Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t) else 0) =
      Pi.single (⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩)
        (((wt t : ℝ) : ℂ) • Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t)) := by
    funext q; simp [Pi.single_apply]
  rw [e, PiLp.norm_toLp_single, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ) ≤ wt t from Real.sqrt_nonneg _)]

end FromFull

section TermReal

variable {D : D7} (X : HidaSetting D)

def frR (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ :=
  Formalism.L2.SG.RealObj.frm X u D.host.rdE v

variable {X} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def ZhatT (t : GTerm X u u' F0 F0' what₂ rows') (v : InfinitePlace X.B.I.F) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
  Formalism.L2.SG.RealObj.ZX X u u' D.host.rdE (t.pt).1 v

def DlT (t : GTerm X u u' F0 F0' what₂ rows') (v : InfinitePlace X.B.I.F) (l : ℕ) : ℂ :=
  Formalism.L2.SG.RealObj.Dl (ZhatT t v) l

def GvT (t : GTerm X u u' F0 F0' what₂ rows') (v : InfinitePlace X.B.I.F) : ℝ :=
  Formalism.L2.SG.RealObj.GX X u u' D.host.rdE (t.pt).1 v

def JvT (t : GTerm X u u' F0 F0' what₂ rows') (v : InfinitePlace X.B.I.F) : X.Vloc u' v →L[ℂ] X.Vloc u v :=
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  Formalism.L2.SG.RealObj.Jv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) ((t.pt).1 v)

end TermReal

section NGData

def toPts {K : Type} [Zero K] {i : ℕ} (p : Formalism.MainNotions.S.Point K (i + 1)) : Σ c : Composition (i + 1), (Fin c.length → K) :=
  ⟨⟨p.1.map Prod.snd, fun {j} hj => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
      exact (p.2.1 b hb).2, p.2.2⟩,
    fun a => (p.1.get ⟨a.1, by simpa [Composition.length] using a.2⟩).1⟩

section Pts

variable {E : Type} [Field E] {r : ℕ}

def endMin (γ : PN.Pts E r) (a : Fin γ.1.length) : E :=
  Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry γ.1.blocksFun γ.2 a

def endIdx (γ : PN.Pts E r) (a : Fin γ.1.length) : ℕ := γ.1.sizeUpTo (a.1 + 1)

def DlastPt (γ : PN.Pts E r) : E :=
  if h : 0 < γ.1.length then endMin γ ⟨γ.1.length - 1, by omega⟩ else 1

def DrPt (γ : PN.Pts E r) : E :=
  if h : 0 < γ.1.length then
    (if γ.1.blocksFun ⟨γ.1.length - 1, by omega⟩ = 1 then
      (if h2 : 2 ≤ γ.1.length then endMin γ ⟨γ.1.length - 2, by omega⟩ else 1) else 0)
  else 1

def GPt [StarRing E] (TT : ℕ) (γ : PN.Pts E r) : E :=
  DlastPt γ * star (DlastPt γ) - (TT : E) * (DrPt γ * star (DrPt γ))

variable [NumberField E]

def NGPt [StarRing E] (rd : ℝ) (TT : ℕ) (γ : PN.Pts E r) : ℝ :=
  ∏ w : InfinitePlace E, (rd ^ (2 * r * (r + 1)))⁻¹ * w (GPt TT γ)

def NDPt (rd : ℝ) (γ : PN.Pts E r) : ℝ :=
  ∏ a : Fin γ.1.length, ∏ w : InfinitePlace E,
    (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2

def nPt [StarRing E] (rd : ℝ) (k TT : ℕ) (γ : PN.Pts E r) : ℝ :=
  ∏ w : InfinitePlace E,
    ((rd ^ (2 * r * (r + 1)))⁻¹ * w (GPt TT γ)) ^ (k - 1) *
      ∏ a : Fin γ.1.length,
        ((rd ^ (2 * r + 1 + γ.1.blocksFun a - 2 * endIdx γ a))⁻¹ * w (γ.2 a)) ^
          (2 * γ.1.blocksFun a * (2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1))

def HPt [StarRing E] (rd g : ℝ) (TT : ℕ) (γ : PN.Pts E r) : ℝ :=
  (g ^ ((2 * r + 1) * Fintype.card (InfinitePlace E)))⁻¹ * NGPt rd TT γ * NDPt rd γ

end Pts

variable {D : D7}

variable {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

abbrev TauC : Type := GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')

variable {Y u u'}

def ptPN (t : TauC Y u u') : PN.Pts D.host.E D.R.rS := toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)

variable (Y u u')

def clsOf (t : TauC Y u u') : Set (TauC Y u u') :=
  {t' | t' ∈ (Y.tO u u').ngSet ∧ (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t ∧ (Y.tO u u').s0 t t' = 1}

def ampS (t : TauC Y u u') : ℂ :=
  (X.volK2 : ℂ) * chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
    ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt)

def J2loc (γ : PN.Pts D.host.E D.R.rS) : ℝ :=
  if h : ∃ t : TauC Y u u', t ∈ (Y.tO u u').ngSet ∧ (Y.tO u u').vec t ≠ 0 ∧ ptPN t = γ then
    ‖Formalism.L2.SG.PackageTie.hsEmb
      (((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') : ℝ) : ℂ) • OOt h.choose)‖ ^ 2
  else 0

def a2Of (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (ν : TauC Y u u') : ℝ :=
  if ν ∈ (Y.tO u u').ngSet ∧ clsOf Y u u' ν = c ∧ ptPN ν = γ then wt ν ^ 2 * ‖ampS Y u u' ν‖ ^ 2 else 0

def ngenOf (γ : PN.Pts D.host.E D.R.rS) : ℝ :=
  ∑' t : TauC Y u u', {t : TauC Y u u' | t.generic ∧ t.G ≠ 0 ∧ ptPN t = γ}.indicator (fun t => wt t ^ 2) t

def NOf : PN.NGData (TauC Y u u') D.host.E D.R.rS (Set (TauC Y u u')) (TauC Y u u') where
  cls := clsOf Y u u'
  pt := ptPN
  nml := id
  a2 := a2Of Y u u'
  J2loc := J2loc Y u u'
  jacobianSquareBound := J2loc Y u u'
  n := nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u' : ℕ))
  NG := NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ))
  ND := NDPt D.host.rdE
  Hh := HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u' : ℕ))
  ngen := ngenOf Y u u'

end NGData

section NGCut

def NGCutC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ (C1 C0n A : ℕ) (CB CSt Cgs CTs : ℝ), 0 ≤ CB ∧ 0 ≤ CSt ∧ 0 ≤ Cgs ∧ 0 ≤ CTs ∧
    C1 + C0n + 38 ≤ A ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie X Y →
      ∃ (P : Type) (_ : Fintype P) (B : S3.MassData P) (cSt e1 Irat Ire : ℝ),
        (Y.tO u u').Gam1 = B.Gam1 ∧ B.d * B.d' / B.Dstar = ddC X Y u u' ∧ PN.NormInputs B ∧
        PN.FrameInputs B (2 * D.host.v) (X.B.g : ℝ) D.R.rS D.R.k D.R.f Irat Ire ∧
        PN.NGSizes Cgs CTs CSt D.R.rS D.R.f large₂.sc.b (2 * D.host.v) (X.B.g : ℝ)
          (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) cSt e1 ∧
        Formalism.L2.SG.RowsOther.NGFin (Y.tO u u') (NOf Y u u') D.R.k D.R.f C1 C0n (2 * D.host.v) (X.B.g : ℝ)
          (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 ∧
        Formalism.L2.SG.RowsOther.NGReal (Y.tO u u') (NOf Y u u') D.R.f A CB large₂.sc.b cSt Ire

theorem rowNGC_of_cut (hR : PN.RowNGJoint) (hC : PN.NGChain) (hc : NGCutC) : RowNGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, A, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0
  obtain ⟨Cn, hCn, hK⟩ := Formalism.L2.SG.RowsOther.rowNG_of_cut hR hC C1 C0n A CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u u' h0 hs hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, hG, hdd, hN, hF, hS, hFin, hRe⟩ := h C' Cl a b D large₂ X Y u u' h0 hs hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u') _ _ _ _ (Y.tO u u') D.R.rS D.R.k (Set (TauC Y u u')) (TauC Y u u')
    (NOf Y u u') P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hFin hRe
  rw [hdd] at r
  exact r

end NGCut

end Formalism.L2.SG.RowsConc
