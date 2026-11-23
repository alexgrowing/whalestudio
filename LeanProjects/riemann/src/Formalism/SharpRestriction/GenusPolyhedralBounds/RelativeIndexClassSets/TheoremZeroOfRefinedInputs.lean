import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLift
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem theorem_zero_of_refined_inputs {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} : Conclusion1OfComb4 (D := D) (B := B) (P := P) := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA _ _ _ G Gc PH Prw Pet Pd
    tW tTh tZ tQ _ dH dS dL pG sRd sRho sRhoP hP iZ iM hQf hDm hM
  by_cases hj : j < D.R.m
  · obtain ⟨Qf, iB, iC, iT, iLf, hB, hHt⟩ := hQf hj
    obtain ⟨hs, hb⟩ := rLa_tsum_le_comb large₂ X K H Ch Ah Cq Aq C2 A2 CR CT h1 h2 S T nP nW h0 nus hH lA sA mA qA G Gc PH Prw
      Pet Pd tW tZ tQ dH dS dL (pageGd4_iff.mp pG) (polyDom4_iff.mp hP) Qf hHt
    have hsum := hb.trans (sumGC4 large₂ (X j h1 h2) h1 K H Ch Ah Cq Aq C2 A2 CR CT S T nP nW h0 nus hH G Gc PH Prw Pet Pd
      tTh dL sRd sRho sRhoP hP Qf hHt)
    refine concl_of_nat (X j h1 h2) S ka wL wF T nus _ (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL))
      hH.2.2.2.1.1 (fun la => rLa_nonneg_comb4 hB la _ _ _) hs hsum (fun la e he V' hV => ?_)

    have hw : ∀ k, G.w k ∈ (X j h1 h2).WWc S.sW wL := fun k => tW.1 ▸ Submodule.subset_span ⟨k, rfl⟩
    have hH2 : H2 (X j h1 h2) S ka wL wF := hH.2.2.2.2.1
    have hth'M : ∀ i, G.th' i ∈ B.Mlat j wF := fun i => hH2.2.1 (tTh i).1
    have hOk : (Qf la).Ok S K.CRm T (cc D large₂ C2 A2 CR wL) := ⟨iB la, iC la, iT la, iZ la, iM la⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT0, hDT, -⟩ := hH.2.1
    exact localBound G la (Qf la) S K.CRm _ e (nus la) (ka_eq_addL_of_setC hH.2.1) lA (theta_le_msup_of_hypC _ S hH)
      (span_Thc_of_hypC hH).2.2 hT0 hDT hw tW.2.1 (fun i => (tTh i).1) hth'M (fun k => (tZ.1 k).1)
      (fun k => (tZ.1 k).2.1) (fun k => (tZ.1 k).2.2.2) tZ.2.1 tZ.2.2 tQ.2.1 tQ.2.2.1 (iB la) (iC la) (iT la) (iM la)
      (vEt_nonneg_comb4 hB la) (nu_le_comb4 hj hB la (iT la)) he
      (lenBase_all j _ ka wL wF G la (Qf la) S K.CRm T _ hOk hth'M hw (hHt.1 la))
      (lenPoleL_all j _ ka wL wF G la (Qf la) S K.CRm T e _ hOk (iLf la tW (iC la) (iT la)) hw) V' hV
  · exact hM (not_lt.1 hj) (hDm (not_lt.1 hj))

end Formalism.MainNotions.Gaps.EtaleWeightGaps
