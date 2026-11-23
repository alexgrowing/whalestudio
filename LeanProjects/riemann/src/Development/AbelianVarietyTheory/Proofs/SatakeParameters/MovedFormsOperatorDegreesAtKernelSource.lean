import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GmOfMapEqActC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteValuesAtPointIffRealisesInStdCoordsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolDYGoodDeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NaturalActionInverseFrameUndoesMoveStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialOfRealisingValueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosTieAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormLevelZeroRealisesComplexPolyStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormNormalisedValuesLatticeTupleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeightsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSiteStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

set_option maxHeartbeats 4000000 in

theorem moved_forms_at_source : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std), ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → ∀ (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) (gmS d) j ∧ TieOpS (Y := S.Y) t u μ (clsAt X H) (gmS d) (sO d ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) ∧ KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  intro d j hjm hne hN
  have hj : j ≤ D.R.m := hjm.le
  have h : ((sysS H X std).Pj j).m + 1 = D.R.N j := rkS _ _ hN
  have hWt := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hjm hne
  have hPT := (posTie_at S hPos ι hι).1
  have hdg : ∀ τ, (t.O u μ).dgen τ ≠ 0 := by
    intro τ h0
    have h1 := GlobalTheory.T.norm_derivation_generators_eq_one_at_site S ι hι τ
    rw [h0, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  have hV : ∀ (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j),
      ((sysS H X std).Pj j).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat j).V, ∃ V : XR ((sysS H X std).Pj j) ℂ,
        MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp j x La.1 La.2) =
          MvPolynomial.map ι V ∧ RealAt d j hj h La ((ex.tw.fm u μ).emb j x) V := by
    intro j
    cases j with
    | zero => intro hj h La hL x; exact GlobalTheory.T.comparedForm_levelZero_realises_complexPoly S hDict hPos ι hι d h La hL x
    | succ k => intro hj h La hL x; exact GlobalTheory.T.comparedForm_normalisedValues_latticeTuple S hDict hPos ι hι d k hj h La hL x
  have core : ∀ La ∈ S.Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, K2.SharpQ t ex.tw u μ j x Q →
      GoodG (sysS H X std) ℂ_[D.what₂.places.resChar w] j (gmS d j La x) ∧ OddDeg (sysS H X std) j (gmS d j La x) ∧
      ∀ n, MvPolynomial.coeff n (polDel (sysS H X std) ℂ_[D.what₂.places.resChar w] j (gmS d j La x)) =
        ι (sPt d j hj La * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) •
          MvPolynomial.coeff n (trDY (sysS H X std) ℂ_[D.what₂.places.resChar w] j D (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)
            (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) (polDY D (t.O u μ).dgen (Q (clsAt X H j La.1 La.2)) (N' := D.R.N (j + 1)))) := by
    intro La hLa x Q hQ
    have hL := S.Y.Rep_lat j La hLa
    obtain ⟨V, hVm, hVr⟩ := hV j hj h La hL x
    have hFr := GlobalTheory.T.changedFrame_rational_unitary S d j hj h La
    have hmap := gmOf_map_eq_actC (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hPT d.fd2 j La h
      (mM d j hj La) hFr.1 hFr.2.1 _ V hVm
    have hφ : ∀ y, (ex.tw.fm u μ).emb j x (clsAt X H j La.1 La.2) y =
        (∏ τ, (D.chTw u μ).de j y τ ^ (D.chTw u μ).sSharp j τ)⁻¹ * frPoly (t.O u μ) j (Q (clsAt X H j La.1 La.2)) y := by
      intro y
      have h2 := congrFun (hQ.2 (clsAt X H j La.1 La.2)) y
      have hne : (∏ τ, (D.chTw u μ).de j y τ ^ (D.chTw u μ).sSharp j τ) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((D.chTw u μ).de_ne j y τ)
      rw [← h2]
      simp only [ColumnChain.sharp, mulFun, LinearMap.coe_mk, AddHom.coe_mk]
      field_simp
    have hR := (GlobalTheory.T.kernelSite_valuesAtPoint_iff_realisesInStdCoords S d j hj h La ((D.chTw u μ).sSharp j) ((ex.tw.fm u μ).emb j x) (Q (clsAt X H j La.1 La.2)) hφ V).1 hVr
    have hw : (fun τ => (D.chTw u μ).sSharp j τ - cTw D j) = wT (sysS H X std) D (hT.gat_pos u w hg) j :=
      funext fun τ => (hWt.sh τ).symm
    rw [hw] at hR
    exact GlobalTheory.T.operatorPolynomial_of_realising_value (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι j hN (nuT D u j) hWt.nu
      (Q (clsAt X H j La.1 La.2)) (hQ.1 _) (sPt d j hj La) _ (gmS d j La x) hR hmap (t.O u μ).dgen hdg
  refine ⟨fun La hLa x => ?_, fun La hLa x Q hQ n => ?_, fun La hLa x Q hQ α hα => ?_⟩
  · obtain ⟨Q, hQ⟩ := J.sharp j hjm x
    obtain ⟨h1, h2, -⟩ := core La hLa x Q hQ
    exact ⟨GlobalTheory.T.naturalAction_inverseFrame_undoes_move (sysS H X std) D (hT.gat_pos u w hg) d.fd2 j La _, h1, h2⟩
  · rw [(core La hLa x Q hQ).2.2 n]
    simp only [sO, dif_pos hj]
  · exact polDY_goodDeg (sysS H X std) D (hT.gat_pos u w hg) j hN (nuT D u j) hWt.nu _ (hQ.1 _) _ α hα

end GlobalTheory.TwV.DelA
