import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleLevelZeroPointIsComponentPoint
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosTieAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

set_option maxHeartbeats 1000000 in

theorem cmp_realAt_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) (h : ((sysS H X std).Pj 0).m + 1 = D.R.N 0) (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat 0).V, ∃ V : XR ((sysS H X std).Pj 0) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp 0 x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d 0 (Nat.zero_le _) h La ((ex.tw.fm u μ).emb 0 x) V) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP ι hι d h La hLa x
  have hpos := (posTie_at S hP ι hι).2
  obtain ⟨g, hg1, hg2⟩ := latticeTupleLevelZero_point_isComponentPoint S hD La hLa
  have hx : x = ex.tw.e0 u μ ((ex.tw.e0 u μ).symm x) := by simp
  generalize (ex.tw.e0 u μ).symm x = x0 at hx
  subst hx
  have K := lev0AtOf_compatible J.Gd.cmp u w hg
  refine ⟨MvPolynomial.map D.what₂.embLL (K.val x0 La.1 La.2), ?_, ?_⟩
  · rw [(kaAt X H hT).cmp_zero, K.val_cmp x0 La.1 La.2 hLa]
    refine (MvPolynomial.map_map _ _ _).trans ((congrArg (MvPolynomial.map · _) ?_).trans (MvPolynomial.map_map _ _ _).symm)
    ext r
    exact (hpos r).symm
  · intro z z' hz
    have hj : (0:ℕ) ≤ D.R.m := Nat.zero_le _
    set c := J.e0.symm (clsAt X H 0 La.1 La.2) with hc
    have hce : clsAt X H 0 La.1 La.2 = J.e0 c := by simp [c]
    have hU := (J.lev0 (J.chart std 0 hj La)).2.2.1
    have hkmem : ((d.kap 0 hj La) : GL (Fin (D.R.N 0)) _) ∈ (J.Gd.forms u).cls0.lev.U := hU ▸ (d.kap 0 hj La).2
    let κ' : (J.Gd.forms u).cls0.lev.U := ⟨(d.kap 0 hj La).1, hkmem⟩
    have hchi := (J.lev0 (J.chart std 0 hj La)).2.2.2 (d.kap 0 hj La) κ' rfl
    obtain ⟨κ0, hy0, hc0, -⟩ := J.y0 c
    have hpt := d.eq 0 hj La hLa
    rw [hce, hy0] at hpt
    have hIs : (lev0At J.Gd u w hg).A.IsPt La.1 g (GlobalTheory.TwU.ratA D.host.F (d.gam 0 hj La) * ((J.Gd.forms u).cls0.y c).1 * (κ0 * κ').1) := by
      convert hg2 using 2
      rw [hpt, Subgroup.coe_mul]
      simp only [mul_assoc]
      rfl
    have hv := K.val_emb x0 La.1 La.2 g hg1 c (d.gam 0 hj La) (d.mem 0 hj La) (κ0 * κ') hIs z z' hz
    have e1 : (((J.Gd.forms u).cls0.lev.chi (κ0 * κ') : ℂˣ) : ℂ) = (((J.Gd.forms u).cls0.lev.chi κ' : ℂˣ) : ℂ) := by
      have e2 := MonoidHom.map_mul (J.Gd.forms u).cls0.lev.chi κ0 κ'
      rw [hc0, one_mul] at e2
      exact congrArg Units.val e2
    rw [e1] at hv
    show _ = _
    rw [cTw_zero]
    simp only [zpow_zero, neg_zero, dPow, detF, Finset.prod_const_one, mul_one]
    refine hv.trans ?_
    have hy : (J.St 0 hj).eY.symm z' = J.jointCmpEmbeddingY ((J.Gd.forms u).val0.eY.symm z') := by
      rw [Equiv.symm_apply_eq, J.fr0, Equiv.apply_symm_apply]
    rw [ex.tw.embed_mul_block_embedding, hce, hy, J.e0Tw, Dec.chi, hchi]

end GlobalTheory.TwV.DelA
