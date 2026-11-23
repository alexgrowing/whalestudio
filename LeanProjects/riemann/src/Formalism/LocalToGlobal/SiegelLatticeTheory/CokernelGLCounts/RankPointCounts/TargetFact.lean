import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocRealAtOrd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcIntGen

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Helpers

variable {K : Type*} [CommRing K] {n : ℕ}

theorem isUp_sconj {S X : Matrix (Fin n) (Fin n) K} (s d d' : Fin n → K) (hS : S = Matrix.diagonal s)
    (hs : ∀ a, s a * s a = 1) (hd : ∀ a, d a * d' a = 1) (hX : IsUp X) :
    IsUp (S * Matrix.diagonal d * X * Matrix.diagonal d' * S) := by
  have e : S * Matrix.diagonal d * X * Matrix.diagonal d' * S =
      Matrix.diagonal (fun a => s a * d a) * X * Matrix.diagonal (fun a => d' a * s a) := by
    rw [hS, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc _ (Matrix.diagonal d'), Matrix.diagonal_mul_diagonal]
  rw [e]
  exact isUp_conj hX _ _ fun a => by
    calc s a * d a * (d' a * s a) = (d a * d' a) * (s a * s a) := by ring
      _ = 1 := by rw [hd, hs, one_mul]

theorem isLo_sconj {S X : Matrix (Fin n) (Fin n) K} (s d d' : Fin n → K) (hS : S = Matrix.diagonal s)
    (hs : ∀ a, s a * s a = 1) (hd : ∀ a, d a * d' a = 1) (hX : IsLo X) :
    IsLo (S * Matrix.diagonal d * X * Matrix.diagonal d' * S) := by
  have e : S * Matrix.diagonal d * X * Matrix.diagonal d' * S =
      Matrix.diagonal (fun a => s a * d a) * X * Matrix.diagonal (fun a => d' a * s a) := by
    rw [hS, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc _ (Matrix.diagonal d'), Matrix.diagonal_mul_diagonal]
  rw [e]
  exact isLo_conj hX _ _ fun a => by
    calc s a * d a * (d' a * s a) = (d a * d' a) * (s a * s a) := by ring
      _ = 1 := by rw [hd, hs, one_mul]

theorem isLo_one' {K : Type*} [CommRing K] {n : ℕ} : IsLo (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne]⟩

theorem isUp_one' {K : Type*} [CommRing K] {n : ℕ} : IsUp (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩

end Helpers

section ClearFp

variable {D : Formalism.BasicNotions.D7}

theorem clear_Fp (p : PlF D) {ι : Type} [Fintype ι] (z : ι → (D.s.atP p).Fp) :
    ∃ c : 𝓞 D.host.F, c ≠ 0 ∧ ∀ k,
      (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c) * z k ∈ (haveI := (D.s.atP p).lf; 𝒪[(D.s.atP p).Fp]) := by
  haveI := (D.s.atP p).lf
  have h := fun k => clear_F (fun q => D.s.atP q) p (z k)
  choose t ht0 htz using h
  refine ⟨∏ k, t k, Finset.prod_ne_zero_iff.2 fun k _ => ht0 k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), map_mul, map_mul,
    mul_comm ((D.s.atP p).ιF (algebraMap _ _ (t k))), mul_assoc]
  exact Subring.mul_mem _ (iotaF_int_mem (fun q => D.s.atP q) p _) (htz k)

end ClearFp

section TypedFact

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)
  (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
  (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Zd.M p).L) (hM : (Zd.M p).split = some g)
  (hge : g.e = sg.e) (hgq : g.q = sg.q)
include hR hM hge hgq

set_option maxHeartbeats 1000000 in

theorem zz_fact (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {L B : PairVal.MatR D} (hL : IsLo L)
    (hB : IsUp B) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) * LsDatumB.sgnP p =
      glue sg.e (Matrix.diagonal (cf Zd p) * L.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))
          (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p)) *
        glue sg.e ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
            (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
              (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS)
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
            (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
              ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS) *
        glue sg.e (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))
          (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) := by
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  set S := Sg (D.s.atP p).Fp D.R.rS with hS
  have hZ : (L * ptMat w * B * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w * B := by
    rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  have hΛ1 : IsLo (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) :=
    isLo_conj (isLo_map φ1 hL) _ _ (cf_cfi Zd p)
  have hV1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map φ1 * Matrix.diagonal (cf Zd p)) :=
    isUp_conj (isUp_map φ1 hB) _ _ (cfi_cf Zd p)
  have hBt : IsLo (S * (B.map φ2).transpose * S) :=
    isLo_conj (isLo_transpose (isUp_map φ2 hB)) _ _ (fun a => sgn_sq' D.R.rS a)
  have hLt : IsUp (S * (L.map φ2).transpose * S) :=
    isUp_conj (isUp_transpose (isLo_map φ2 hL)) _ _ (fun a => sgn_sq' D.R.rS a)
  have hΛ2 : IsLo (Matrix.diagonal (cf Zd p) * (S * (B.map φ2).transpose * S) * Matrix.diagonal (cfi Zd p)) :=
    isLo_conj hBt _ _ (cf_cfi Zd p)
  have hV2 : IsUp (Matrix.diagonal (cfi Zd p) * (S * (L.map φ2).transpose * S) * Matrix.diagonal (cf Zd p)) :=
    isUp_conj hLt _ _ (cfi_cf Zd p)
  refine mat_eq sg.e ?_ ?_
  · have l1 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) *
        LsDatumB.sgnP p).map (p1 sg.e) =
        (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) *
          ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map φ1 * Matrix.diagonal (cf Zd p))) *
          (Matrix.diagonal (cfi Zd p) * B.map φ1 * Matrix.diagonal (cf Zd p)) -
        (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
      rw [zz1' Zd p sg hR g hM hge hgq, hZ, Matrix.map_mul, Matrix.map_mul, fact1 _ _ (cfi_cf Zd p)]
    rw [l1, Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, glue_map_fst, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hΛ1 hV1]
  · have e2 : ((L * ptMat w * B * Sg D.host.E D.R.rS).map φ2).transpose * S =
        (S * (B.map φ2).transpose * S) * (S * (ptMat w).map φ2 * S) * (S * (L.map φ2).transpose * S) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
      exact fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])
    have l2 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) *
        LsDatumB.sgnP p).map (p2 sg.e) =
        (Matrix.diagonal (cf Zd p) * (S * (B.map φ2).transpose * S) * Matrix.diagonal (cfi Zd p)) *
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (S * (ptMat w).map φ2 * S) *
            Matrix.diagonal (cf Zd p))) *
          (Matrix.diagonal (cfi Zd p) * (S * (L.map φ2).transpose * S) * Matrix.diagonal (cf Zd p)) -
        ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
      rw [zz2' Zd p sg hR g hM hge hgq, e2, fact1 _ _ (cfi_cf Zd p)]
    rw [l2, Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, glue_map_snd, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hΛ2 hV2]

set_option maxHeartbeats 1000000 in

theorem target_fact (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) :
    ∃ Gl Gu : MatP D p, IsLo Gl ∧ IsUp Gu ∧
      glue sg.e ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
            (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
              (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS)
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
            (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
              ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS) =
        Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0 :=
    fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  obtain ⟨L1, U1, hL1, hU1, h1⟩ := generic_comp (sgF w) (sgF_sgF _) (isLo_one' (K := (D.s.atP p).Fp))
    (isUp_one' (K := (D.s.atP p).Fp))
    (W := (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE))
    (fun a b hb => by simp only [Matrix.map_apply, ptMat_apply', if_neg hb, map_zero])
    (fun a => by
      simp only [Matrix.map_apply, ptMat_apply', if_true]
      exact (map_ne_zero _).2 (pTau_ne' _ a))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (sg.q : (D.s.atP p).Fp)⁻¹ (inv_ne_zero hq)
    (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  obtain ⟨L2, U2, hL2, hU2, h2⟩ := generic_comp (sgF w) (sgF_sgF _) (isLo_one' (K := (D.s.atP p).Fp))
    (isUp_one' (K := (D.s.atP p).Fp))
    (W := Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS)
    (fun a b hb => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb, map_zero,
        mul_zero, zero_mul])
    (fun a => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true]
      exact mul_ne_zero (mul_ne_zero (hs0 _) ((map_ne_zero _).2 (pTau_ne' _ a))) (hs0 _))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (-(sg.q : (D.s.atP p).Fp)⁻¹) (neg_ne_zero.2 (inv_ne_zero hq))
    ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  rw [Matrix.one_mul, Matrix.mul_one] at h1 h2
  refine ⟨glue sg.e L1 L2, glue sg.e U1 U2, isLo_glue sg.e hL1 hL2, isUp_glue sg.e hU1 hU2, mat_eq sg.e ?_ ?_⟩
  · rw [glue_map_fst, h1, Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, mm1' Zd p sg hR g hM hge hgq]
  · rw [glue_map_snd, h2, Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, mm2' Zd p sg hR g hM hge hgq]

end TypedFact

end Formalism.L2.SG.Pf.PCountEx
