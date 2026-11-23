import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.VanishingOrderLeWeightSize
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PvsDimYPos

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem deepC (large₂ : SizeData₂ D) (X : PJ D B P j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T nP nW : ℕ) (h0 CK C1 A1 Gc Prw CG AG p Pd : ℝ)
    (hC : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0)
    (tW : G.TiedW S Gc Prw) (tZ : G.TiedZ S T Gc) (dH : DeepHerm X ka) (dS : DeepSubMul X) (dL : DeepLogD X ka Pd)
    (pG : PageGd X ka large₂ CG AG Pd) (hG0 : 0 ≤ Gc) (hP0 : 0 ≤ Prw)
    (hlat : Submodule.IsLattice B.KO (B.Mlat j ka))
    (hLAM : ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 → -(p * ka.size) ≤ WeightFamilies.meanLogSup B F)
    (hS2 : ∀ (F : B.Cusp j ka) (σ : B.KO →+* ℂ), B.supN j ka σ F ^ 2 ≤
      Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * B.l2NormAlt j ka σ F ^ 2) :
    Summable (fun la => (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la) ∧
      ∑' la, (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la ≤
        G.rz * ((2 * Gc + Prw + p + 3 / 2 * (Pd + PO D large₂)) * ka.size) := by
  obtain ⟨hk, -, -, -, -, -, -, -, -, -, -, -, -, hV, hIL, hIF, -, -, hD, -, -, h40, -, -, hO, -⟩ := hC
  obtain ⟨-, hwM, hrw, hmx, hmxm⟩ := tW
  obtain ⟨hz0, hz, hWd⟩ := tZ
  obtain ⟨dd, Hm, hconj⟩ := dH
  have hwt := SizeBoundsAlt.hwt_of X ka wL wF T nP nW hIF hIL.1 (hk.trans hV) hD
  obtain ⟨z', hz1, hz2⟩ := SizeBoundsAlt.exists_zFam X ka wL (X.wF0 wL wF) (a0 D j T) hwt G.w hwM G.th0 (fun k => (hz0 k).2.1)
    G.alz (fun k => (hz0 k).2.2.2)
  have hzM : ∀ k β, G.zc k β ∈ B.Mlat j ka := by
    intro k β
    have : G.zc k β = z' k β := X.inc_inj ka ((hz k β).trans (hz1 k β).symm)
    rw [this]; exact hz2 k β
  exact deepPacketP large₂ X ka wL (X.wF0 wL wF) (a0 D j T) hwt G.w G.th0 G.alz (fun k => (hz0 k).2.2.2) G.zc hz _
    (fun la => SizeBoundsAlt.gaussC_nonneg _ G.zc la) (SizeBoundsAlt.gaussC_gaussLe hzM) hWd Hm
    (fun Ctr hC => SizeBoundsAlt.trans_of_minima _root_.transference_successive_minima _ hlat.span_eq_top Hm hconj Ctr hC)
    dS p hLAM Gc Prw Pd
    (fun σ F => (hS2 F σ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr pG) (sq_nonneg _)))
    hG0 hP0 G.mx (fun σ k => (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (hmx σ k))) hmxm
    (fun k => (hz0 k).2.2.1) (vanishingOrder_le_weight_size ka T nP nW (hk.trans hV) (lt_of_lt_of_le (by norm_num) h40)) hrw dL hO

theorem quotC {large₂ : SizeData₂ D} {X : PJ D B P j} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    {Gc PH Prw Pet Pd : ℝ}
    (hQ : j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL))
    (hH : HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (G : GlobalFamilyData X ka wL wF)
    (tQ : G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) :
    Summable (fun la => lenQ G K.CRm T (cc D large₂ C2 A2 CR wL) la * X.lN la) ∧
      ∑' la, lenQ G K.CRm T (cc D large₂ C2 A2 CR wL) la * X.lN la ≤ 2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  by_cases hj : j < D.R.m
  · obtain ⟨-, hS, -, -, -, h3, -, -⟩ := hH
    obtain ⟨hrq, -, hspan, hsup⟩ := tQ
    have hT : 0 < T := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact (quotCoreE large₂ ka (T : ℝ) (cc D large₂ C2 A2 CR wL)
      (hQ hj (le_trans (by norm_num) hP.1) hP.2.2.2.2.2.1 hS.1 (lastPos_of_SetC hS) hS.2.2.2.2.2.2.2.1
        (by exact_mod_cast hT) (cc_pos_of hS h3 hP) (T_mul_cc_le_one h3 hP)) G.rq hrq G.th hspan hsup).2
  · obtain ⟨hs, h0'⟩ := lenQ_tsum_of_ge (X := X) G (not_lt.1 hj) K.CRm T (cc D large₂ C2 A2 CR wL)
    refine ⟨hs, ?_⟩
    have hrq : G.rq = 0 := by
      rw [tQ.1]
      exact rhoP_eq_zero_of_rho (rho_eq_zero_of_ge (not_lt.1 hj)) _ _ _ ka
    rw [h0', hrq]
    simp

theorem rLa_tsum_le_comb (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) {ka wL wF : WeightFamilies.Wt D j}
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (lA : LatAt B j ka) (sA : SupBoundByL2AtWeight large₂ B j ka K.CG K.AG) (mA : LAMwAt large₂ B j ka K.CL K.AL)
    (qA : j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL))
    (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (tW : G.TiedW S Gc Prw) (tZ : G.TiedZ S T Gc) (tQ : G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah)
    (dH : DeepHerm (X j h1 h2) ka) (dS : DeepSubMul (X j h1 h2)) (dL : DeepLogD (X j h1 h2) ka Pd)
    (pG : PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
    (Qf : ∀ la, LocalPointData G la) (hHt : Heights Qf Gc PH Prw Pet) :
    Summable (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la) ∧
    ∑' la, rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la ≤
      (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((∑' la, ((Qf la).Ila.toNat : ℝ) * (X j h1 h2).lN la) +
        (if j < D.R.m then (T : ℝ) * (max 0 (cc D large₂ C2 A2 CR wL) / (2 * (G.iet : ℝ))) *
          ∑' la, (Qf la).Net * (X j h1 h2).lN la else 0)) +
      G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) +
      2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  obtain ⟨hCs, hCb⟩ := deepC large₂ (X j h1 h2) G S T nP nW h0 H.CK H.C1 H.A1 Gc Prw K.CG K.AG
    (WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size)) Pd hH.2.1 tW tZ dH dS dL pG hP.2.2.1 hP.2.2.2.1 lA mA sA
  obtain ⟨hQs, hQb⟩ := quotC qA hH G tQ hP
  obtain ⟨hs, he⟩ := rLa_tsum_split Qf K.CRm T (cc D large₂ C2 A2 CR wL) hHt.2.1 (fun hj => (hHt.2.2.2 hj).1) hCs hQs
  refine ⟨hs, ?_⟩
  rw [he]
  linarith

theorem sumC : SumC D B P := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA G Gc PH Prw Pet Pd
    tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP hB Qf hHt
  obtain ⟨hs, hb⟩ := rLa_tsum_le_comb large₂ X K H Ch Ah Cq Aq C2 A2 CR CT h1 h2 S T nP nW h0 nus hH lA sA mA qA G Gc PH Prw Pet Pd
    tW tZ tQ dH dS dL pG hP Qf hHt
  exact ⟨hs, hb.trans (sumGC large₂ (X j h1 h2) h1 K H Ch Ah Cq Aq C2 A2 CR CT S T nP nW h0 nus hH G Gc PH Prw Pet Pd
    tTh dL sRd sRho sRhoP hP Qf hHt)⟩

theorem theorem_zero_split_of_local (hL : LocalC D B P) : Conclusion1OfComb (D := D) (B := B) (P := P) := theorem_zero_split_of_local_and_sum hL sumC

end Formalism.MainNotions.Gaps.EtaleWeightGaps
