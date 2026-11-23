import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RankZeroOfLevelThree
import Formalism.LocalToGlobal.BaseRankEqOfRealisation
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Top.smallLevelRankEq_closed_of_levelProjection_surjective : ∀ (𝒜 : FamClass)
    (sel : Formalism.L2.TSel 𝒜)
    (selS : SelS 𝒜 sel)
    (selP : BaseLevelCompatibleSelection 𝒜 sel)
    (selDH : SelDH 𝒜 sel)
    (selC : ColumnCompatibleSelection 𝒜 sel selP)
    (selB : SelB 𝒜 sel selS selP selDH selC)
    (hPA : PrimAll sel (selIOf selB))
    (hLamP : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.Rows.RowsHoldLam3 (selP Fm hc x hx h i).1)
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (zL : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) (selP Fm (d3_a hc) x hx h i).1.A3.A (selP Fm (d3_a hc) x hx h i).1.P0
          (selP Fm (d3_a hc) x hx h i).1.ψ0 ((selP Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 (selP Fm (d3_a hc) x hx h i).1.Zs) k
          (selP Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec), Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm := by
  intro 𝒜 sel selS selP selDH selC selB hPA hLamP hDivG zL
  have hDivR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps
        (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I :=
    fun Fm hc x hx h i => (hDivG Fm hc x hx h i).toRows (Formalism.IndefR.LevelRealisationRankEquality.tupAllUsed_of_real (selB Fm hc x hx h i).Q)
  have hZ : Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm :=
    closed_of_mem (zL.imp fun Fm _ _ h hc => by
      obtain ⟨xr, h⟩ := h hc
      exact Formalism.L2.N.RankZeroOfLevelThree.rank_zero_of_row_conditions Fm (max (sel Fm (d3_a hc)).1 xr)
        (fun x hx h0 i => ((sel Fm (d3_a hc)).2 x hx (le_trans (le_max_left _ _) h0) i).T)
        (fun x hx h0 i => (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).1)
        (fun x hx h0 i => (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).2)
        (fun x hx h0 i => hLamP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => hDivR Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => rowsHold0_of hPA Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => ⟨_, (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).1.tied.div.tup.mu0,
          h x hx (le_trans (le_max_left _ _) h0) (le_trans (le_max_right _ _) h0) i⟩))
  exact hZ

end
