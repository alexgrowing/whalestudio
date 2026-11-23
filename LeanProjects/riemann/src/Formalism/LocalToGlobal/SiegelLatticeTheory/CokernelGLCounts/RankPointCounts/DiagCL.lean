import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanDiagonalOfConditions
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.FourierDecayAlt

namespace Formalism.L2.SG.RowsConc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DiagCL : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ CB C4 : ℝ, 0 ≤ CB ∧ 0 ≤ C4 ∧ ∀ CG : ℝ, max CB C4 + 1 ≤ CG → ∃ C'₀ Cl₀ : ℝ,
    ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT →
      ConcTie X Y → (Y.tO u u).AbsConv → large₂.CGam = CG →
      (Y.tO u u).RowBig (epsL D) (ddC X Y u u) → (Y.tO u u).RowNotScalar (epsL D) (ddC X Y u u) →
      Formalism.L2.SG.RowsOther.DiagRow (Y.tO u u) (oneC X Y u) (D.mem u).A.GamP (ddC X Y u u)

theorem diagCL_of_rows (hA : PB.PairBoundAbstract) (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit)
    (hSub : PB.SubFamily) (hGG : Formalism.L2.SG.GGMirabolic.TermsGGBound)
    (hNS : NormExpSatTied) (hC : CorankPosC) (hId : IdOneC) (hNG : RowNGC) (hM : RowMainEqC)
    (hNum : DiagNumC) : DiagCL := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨CB, hCB, C'₁, Cl₁, hM'⟩ := hM Cg cb Cw cT CT C0 A
  obtain ⟨C4, hC4, C'₂, Cl₂, hNG'⟩ := hNG Cg cb Cw cT CT C0
  obtain ⟨C'₄, Cl₄, hNum'⟩ := hNum Cg cb Cw cT CT C0 A CB C4 hCB hC4
  refine ⟨CB, C4, hCB, hC4, fun CG hCG => ⟨max (max C'₁ C'₂) C'₄, max (max Cl₁ Cl₂) Cl₄,
    fun C' Cl h1 h2 D large₂ X Y u hH hK2 hT ha hG r1 r2 => ?_⟩⟩
  have a1 : C'₁ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
  have a2 : C'₂ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1
  have a4 : C'₄ ≤ C' := le_trans (le_max_right _ _) h1
  have b1 : Cl₁ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h2
  have b2 : Cl₂ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
  have b4 : Cl₄ ≤ Cl := le_trans (le_max_right _ _) h2
  have h0 : Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 := hH.1
  have hs : Formalism.MainNotions.S.Cnt.Stand D u u := hH.2.1
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdd := dd_nonneg hT u u
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
  exact hD.trans (mul_le_mul_of_nonneg_right (hNum' C' Cl a4 b4 D large₂ X Y u hH hK2 hT (hG ▸ hCG)) hdd)

end Formalism.L2.SG.RowsConc
