import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowsAbsVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairAmpConstWd
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LiftOntoCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AutLzFinite

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.SpectralTiesReal

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

def AmpValLowerAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
    (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' →
      NuQPin T.X u u' νq →
      Formalism.L2.SG.Pf.RowForm.ClassAbs.AmpValLowerC T.X T.Y u u'
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) i0 i0' νq

theorem tprod_alpD_pos (D : D7) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word) :
    0 < ∏' p, alpD u u' p := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have hαb := Formalism.L2.SG.Pf.alpBound_holds D hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  have hlogα : Summable fun p => Real.log (alpD u u' p) := by
    refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
    have h2 := Real.log_le_log (hal0 p) (hαb p).2
    rw [Real.log_exp] at h1 h2
    constructor <;> linarith
  rw [← Real.rexp_tsum_eq_tprod hal0 hlogα]
  exact Real.exp_pos _

theorem rowsSumC_of (hFC : FormulaC) (hAV : AmpValLowerAll) : RowsSumC := by
  intro D T u u' i0 i0' νq Lsp κ hne hSt hCT _hg3 hk hcong hi hPR hNu hRL
  have hWD : Formalism.L2.SG.WuDecay.WuDecay T.X := hCT.2.2.2.2.1
  have hAbs : (T.Y.tO u u').AbsConv :=
    Formalism.L2.SG.Pf.absConvC_outright D T.X T.Y u u'
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u' (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Pf.fundExistsC_holds D T.X T.Y u u')
      (Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := T.Y) hWD u u')
  have hL := Formalism.L2.SG.Pf.liftOntoC_of (fun D => Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) D T.X T.Y u u'
  have hAF : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u) (T.Y.what₂ u) := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u).A.T_prime.pos (T.X.Fu u) Λ ((T.Y.rowsOK u).1 Λ hΛ)
  have hAF' : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u') (T.Y.what₂ u') := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u').A.T_prime.pos (T.X.Fu u') Λ ((T.Y.rowsOK u').1 Λ hΛ)
  have hLT : Formalism.L2.SG.Pf.LocCP.LocTied D := by
    obtain ⟨_, _, _, _, _, _, _, hL⟩ := hCT.2.2.2.2.2.2.1
    exact hL
  have hnc : 0 < Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u) * ∏' p, alpD u u' p :=
    mul_pos (hFC D T u u' Lsp hLT hSt hcong).1 (tprod_alpD_pos D hk u u')
  exact Formalism.L2.SG.RowsAbsX.rowsSum_of_val _ κ _ i0 i0' (T.Y.FN u) (T.Y.FN u') νq hAbs hL
    (hAV D T u u' i0 i0' νq hne hSt hCT hi hPR hNu) hAF hAF' hnc

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
