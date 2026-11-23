import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ScalKindPf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SmoothBigCellSectionsExist

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ThSomePf

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.LocUnramB
open Formalism.L2.SG.LsDatumB
open scoped Matrix

section MonoU

variable {K : Type} [CommRing K] {m : ℕ}

structure MonoU (W : Matrix (Fin m) (Fin m) K) where
  σ : Fin m → Fin m
  c : Fin m → K
  σσ : ∀ a, σ (σ a) = a
  cσ : ∀ a, c (σ a) = c a
  hcu : ∀ a, IsUnit (c a)
  hW : ∀ a b, W a b = if b = σ a then c a else 0

theorem MonoU.det_unit {W : Matrix (Fin m) (Fin m) K} (H : MonoU W) : IsUnit W.det := by
  let inv : Matrix (Fin m) (Fin m) K := fun a b => if b = H.σ a then Ring.inverse (H.c a) else 0
  have h : W * inv = 1 := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (H.σ a)]
    · rw [H.hW, if_pos rfl]
      simp only [inv]
      by_cases hb : b = a
      · subst hb; rw [if_pos (H.σσ b).symm, H.cσ, Matrix.one_apply_eq, Ring.mul_inverse_cancel _ (H.hcu b)]
      · rw [if_neg (fun h => hb (by rw [h, H.σσ])), mul_zero, Matrix.one_apply_ne (Ne.symm hb)]
    · intro k _ hk; rw [H.hW, if_neg hk, zero_mul]
    · simp
  exact Matrix.isUnit_det_of_right_inverse h

end MonoU

section Corner

variable {K : Type} [Field K] {r : ℕ}

theorem det_add_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (A + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0).det =
      A.det + c * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have e : (A + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0) =
      A.updateCol (Fin.last r) ((fun a => A a (Fin.last r)) + (Pi.single (Fin.last r) c : Fin (r + 1) → K)) := by
    ext a b
    by_cases hb : b = Fin.last r
    · subst hb
      rw [Matrix.updateCol_self]
      by_cases ha : a = Fin.last r
      · subst ha; simp
      · simp [ha, Pi.single_eq_of_ne ha]
    · rw [Matrix.updateCol_ne hb]
      simp [hb]
  rw [e, Matrix.det_updateCol_add, Formalism.L2.SG.Pf.ScalKindPf.det_updateCol_last_single]
  congr 1
  rw [Matrix.updateCol_eq_self]

end Corner

end Formalism.L2.SG.Pf.ThSomePf

namespace Formalism.L2.SG.Pf.ThSomePf

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.LocUnramB
open Formalism.L2.SG.LsDatumB
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeL

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem blkMod_unitL (T T' : ℕ) (p : PlF D) (hA : Agree δ M p) (hsM : (M p).split = none) {t : D.host.E}
    (ht0 : t ≠ 0) (a s : ℕ) :
    IsUnit (blkMod δ T T' p a s t) ∧ (nu D.R.rS a (a + s - 1) = 0 → blkMod δ T T' p a s t = (D.s.atP p).ιE t) := by
  have hsD : (D.s.atP p).split = none := LocModel.split_none_of_agree hA hsM
  obtain ⟨-, hδ0, -, -, -, -⟩ := hA
  set w0 : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)
    with hw0
  set w1 : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ *
    (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw1
  have hw01 : w0 * w1 = 1 := by
    rw [hw0, hw1, mul_mul_mul_comm, ← map_mul, ← map_mul, mul_inv_cancel₀ hδ0,
      mul_inv_cancel₀ (by exact_mod_cast LocModel.unitAt_ne_zero₂ p), map_one, map_one, one_mul]
  have htau : tau0 p T T' = 0 := by simp only [tau0, hsD]
  have hb : blkMod δ T T' p a s t = w1 ^ nu D.R.rS a (a + s - 1) * (D.s.atP p).ιE t := by
    simp only [blkMod, htau, ite_self, sub_zero, tMod, twist, qE, hsD, Ring.inverse_one, mul_one]
    rw [LocModel.ring_inverse_pow_eq hw01]
  have hw1u : IsUnit w1 := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hw01)
  have htu : IsUnit ((D.s.atP p).ιE t) := (isUnit_iff_ne_zero.2 ht0).map _
  rw [hb]
  exact ⟨(hw1u.pow _).mul htu, fun h0 => by rw [h0, pow_zero, one_mul]⟩

theorem monoShiftL (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : Agree δ M p)
    (hsM : (M p).split = none) :
    IsUnit (modMat δ T T' p w + cornerM p (cornerSh δ T T' p w)).det := by
  have hcu : ∀ a : Fin (D.R.rS + 1), IsUnit (blkMod δ T T' p (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val)) :=
    fun a => (blkMod_unitL T T' p hA hsM (pTau_ne' w a) _ _).1
  let H : MonoU (modMat δ T T' p w) :=
    { σ := sgF w
      c := fun a => blkMod δ T T' p (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val)
      σσ := sgF_sgF w
      cσ := fun a => by simp only [sgF]; rw [pSt_pSig, pSz_pSig, pTau_pSig]
      hcu := hcu
      hW := modMat_apply' δ T T' p w }
  by_cases hD : Dmin w D.R.rS = 0
  · have : cornerSh δ T T' p w = 0 := by unfold cornerSh; rw [if_pos hD]
    rw [this]
    have h0 : cornerM p (0 : (D.s.atP p).Ep) = 0 := by ext a b; simp [cornerM]
    rw [h0, add_zero]
    exact H.det_unit
  obtain ⟨l0, t, hb, hs⟩ := last_one w hD
  have hz : zetaOf w = t := zeta_snoc w hD l0 t hb hs
  have ht0 : t ≠ 0 := (w.2.1 (t, 1) (by rw [hb]; simp)).1
  have hpm := ptMat_last w l0 t hb hs
  rw [ptMat_apply'] at hpm
  have hσl : sgF w (Fin.last _) = Fin.last _ := by
    by_contra h
    rw [if_neg (Ne.symm h)] at hpm
    exact ht0 hpm.symm
  rw [if_pos hσl.symm] at hpm
  obtain ⟨c1, c2⟩ := (cond_iff w (Fin.last _)).2 ⟨rfl, hσl⟩
  have hst : pSt w.1 (Fin.last D.R.rS).val = D.R.rS := by
    simp only [Fin.val_last] at c1 c2 ⊢; omega
  have hcl : H.c (Fin.last _) = blkMod δ T T' p (D.R.rS + 1) 1 t := by
    show blkMod δ T T' p (1 + pSt w.1 (Fin.last D.R.rS).val) (pSz w.1 (Fin.last D.R.rS).val)
      (pTau w.1 (Fin.last D.R.rS).val) = _
    rw [c2, hpm, hst, add_comm]
  have hcu_l := H.hcu (Fin.last _)
  rw [hcl] at hcu_l
  have hcs : cornerSh δ T T' p w = ((nSh (blkMod δ T T' p (D.R.rS + 1) 1 t) : ℕ) : (D.s.atP p).Ep) := by
    unfold cornerSh; rw [if_neg hD, hz]
  have hc : ∃ k : Fin 3, IsUnit (blkMod δ T T' p (D.R.rS + 1) 1 t + (((k : Fin 3) : ℕ) : (D.s.atP p).Ep)) :=
    ⟨0, by simpa using hcu_l⟩
  have hnsh : nSh (blkMod δ T T' p (D.R.rS + 1) 1 t) = ((hc.choose : Fin 3) : ℕ) := by
    unfold nSh; rw [dif_pos hc]
  have hku := hc.choose_spec
  let c' : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a =>
    if a = Fin.last _ then blkMod δ T T' p (D.R.rS + 1) 1 t + (((hc.choose : Fin 3) : ℕ) : (D.s.atP p).Ep)
    else H.c a
  have hσne : ∀ a, a ≠ Fin.last _ → H.σ a ≠ Fin.last _ := fun a ha h =>
    ha (by rw [← H.σσ a, h]; exact hσl)
  let H' : MonoU (modMat δ T T' p w + cornerM p (cornerSh δ T T' p w)) :=
    { σ := H.σ
      c := c'
      σσ := H.σσ
      cσ := fun a => by
        by_cases ha : a = Fin.last _
        · have hs' : H.σ a = Fin.last _ := by rw [ha]; exact hσl
          simp only [c', if_pos hs', if_pos ha]
        · simp only [c', if_neg ha, if_neg (hσne a ha)]; exact H.cσ a
      hcu := fun a => by
        by_cases ha : a = Fin.last _
        · simp only [c', if_pos ha]; exact hku
        · simp only [c', if_neg ha]; exact H.hcu a
      hW := fun a b => by
        rw [Matrix.add_apply, H.hW]
        simp only [cornerM, Matrix.of_apply, c']
        by_cases ha : a = Fin.last _
        · have hs' : H.σ a = Fin.last _ := by rw [ha]; exact hσl
          by_cases hbl : b = Fin.last _
          · have hb' : b = H.σ a := by rw [hs', hbl]
            rw [if_pos hb', if_pos ⟨ha, hbl⟩, if_pos hb', if_pos ha, ha, hcl, hcs, hnsh]
          · have hb' : ¬ b = H.σ a := by rw [hs']; exact hbl
            rw [if_neg hb', if_neg (show ¬ (a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS) from fun h => hbl h.2),
              if_neg hb', add_zero]
        · rw [if_neg (show ¬ (a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS) from fun h => ha h.1), add_zero]
          by_cases hb' : b = H.σ a
          · rw [if_pos hb', if_pos hb', if_neg ha]
          · rw [if_neg hb', if_neg hb'] }
  exact H'.det_unit

end ModeL

end Formalism.L2.SG.Pf.ThSomePf

namespace Formalism.L2.SG.Pf.ThSomePf

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.LocUnramB
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section DetL

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem zhatLoc_eq (hA : ∀ p, Agree δ M p) (p : PlF D) (Z : Formalism.L2.SG.PairVal.MatR D) (a b : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.CntLocal.ZhatLoc M δ p Z a b =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf ⟨δ, M, hA⟩ p b * cf ⟨δ, M, hA⟩ p a) * (D.s.atP p).ιE (Z a b) := by
  have e1 : frFac δ p a = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf ⟨δ, M, hA⟩ p a) :=
    frFac_eq (⟨δ, M, hA⟩ : LocDat D) p a
  have e2 : frFac δ p b = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf ⟨δ, M, hA⟩ p b) :=
    frFac_eq (⟨δ, M, hA⟩ : LocDat D) p b
  simp only [Formalism.L2.SG.CntLocal.ZhatLoc, Matrix.of_apply]
  rw [e1, e2, (hA p).2.2.1, cj_alg, ← map_mul]

theorem isUnit_det_signMatrix (p : PlF D) : IsUnit (LsDatumB.sgnP p).det :=
  Matrix.isUnit_det_of_right_inverse (permSign_mul_self₂ p)

theorem detL (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (p : PlF D) (hM : (M p).split = none)
    (w : Point D.host.E (D.R.rS + 1)) (Z : Formalism.L2.SG.PairVal.MatR D) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hL : IsLo L) (hU : IsUp U) (hZ : Z * Sg D.host.E D.R.rS = L * ptMat w * U) :
    IsUnit (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z +
      cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)).det := by
  have hY : Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z * LsDatumB.sgnP p =
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) *
        (Z * Sg D.host.E D.R.rS).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) := by
    have e0 : Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z = Formalism.L2.SG.CntLocal.ZhatLoc M δ p Z := by
      simp only [Formalism.L2.SG.CntLocal.ZZP, Loc.HermSp.ZZplusOf, hM]
    rw [e0]
    ext a b
    simp only [LsDatumB.sgnP, Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    rw [zhatLoc_eq hA p Z a b]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hR : (D.s.atP p).split = none := LocModel.split_none_of_agree (hA p) hM
  set ι := (D.s.atP p).ιE
  set al := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
  set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cf Zd p a)
  set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cfi Zd p a)
  have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
  have hfr' : ∀ a, fr a * fri a = 1 := fun a => by simp only [fr, fri, ← map_mul, cf_cfi, map_one]
  have hmod : Matrix.diagonal fr * (ptMat w).map ι * Matrix.diagonal fr =
      modMat δ (D.mem u).A.T (D.mem u').A.T p w := by
    ext a b
    rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
    by_cases hb : b = sgF w a
    · rw [if_pos hb, if_pos hb, modMat_blk Zd]
      simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul, fr]
      subst hb
      ring
    · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]
  set L' := Matrix.diagonal fr * L.map ι * Matrix.diagonal fri
  set U' := Matrix.diagonal fri * U.map ι * Matrix.diagonal fr
  have hL' : IsLo L' := isLo_conj (isLo_map ι hL) fr fri hfr'
  have hU' : IsUp U' := isUp_conj (isUp_map ι hU) fri fr hfr
  have e1 : Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z * LsDatumB.sgnP p =
      L' * modMat δ (D.mem u).A.T (D.mem u').A.T p w * U' := by
    rw [hY, hZ, Matrix.map_mul, Matrix.map_mul, regroup fr fri hfr, hmod]
  have e2 : Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z =
      L' * modMat δ (D.mem u).A.T (D.mem u').A.T p w * U' * LsDatumB.sgnP p := by
    rw [← e1, Matrix.mul_assoc, permSign_mul_self₂, Matrix.mul_one]
  have e3 : Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w) =
      L' * (modMat δ (D.mem u).A.T (D.mem u').A.T p w + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)) *
        U' * LsDatumB.sgnP p := by
    rw [e2, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, loU_corner p _ ⟨hL'.1, hL'.2⟩ ⟨hU'.1, fun a b h => hU'.2 b a h⟩,
      corner_sgn]
  rw [e3, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_lo hL', det_up hU', one_mul, mul_one]
  exact (monoShiftL _ _ w p (hA p) hM).mul (isUnit_det_signMatrix p)

end DetL

end Formalism.L2.SG.Pf.ThSomePf

namespace Formalism.L2.SG.Pf.ThSomePf

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.LocUnramB
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section DetG

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def cornerF {K : Type} [Field K] (r : ℕ) (c : K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0

theorem det_diag_mul {K : Type} [Field K] {r : ℕ} (f : Fin (r + 1) → K) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (c : K) :
    (Matrix.of (fun a b => f a * A a b * f b) + cornerF r c).det =
      (∏ a : Fin r, f (Fin.castSucc a)) ^ 2 * f (Fin.last r) ^ 2 * A.det +
        c * ((∏ a : Fin r, f (Fin.castSucc a)) ^ 2 * (A.submatrix Fin.castSucc Fin.castSucc).det) := by
  have e1 := det_add_corner (Matrix.of (fun a b => f a * A a b * f b)) c
  unfold cornerF
  rw [e1]
  have h1 : (Matrix.of (fun a b => f a * A a b * f b)) = Matrix.diagonal f * A * Matrix.diagonal f := by
    ext a b; simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h2 : (Matrix.of (fun a b => f a * A a b * f b)).submatrix Fin.castSucc Fin.castSucc =
      Matrix.diagonal (fun a : Fin r => f (Fin.castSucc a)) * A.submatrix Fin.castSucc Fin.castSucc *
        Matrix.diagonal (fun a : Fin r => f (Fin.castSucc a)) := by
    ext a b; simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [h2, h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, Fin.prod_univ_castSucc]
  ring

end DetG

end Formalism.L2.SG.Pf.ThSomePf

namespace Formalism.L2.SG.Pf.ThSomePf

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.LocUnramB
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section DetG2

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem proj_inverse_algebraMap {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] [Nontrivial K] (e : K ≃ₐ[Fp] Fp × Fp)
    (q : Fp) (hq : q ≠ 0) : p1 e (Ring.inverse (algebraMap Fp K q)) = q⁻¹ ∧ p2 e (Ring.inverse (algebraMap Fp K q)) = q⁻¹ := by
  have h1 : algebraMap Fp K q * algebraMap Fp K q⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  have h := LocModel.ring_inverse_pow_eq h1 1
  rw [pow_one, pow_one] at h
  rw [h, fst_proj_algebraMap, snd_proj_algebraMap]
  exact ⟨rfl, rfl⟩

theorem firstProj_det_corner (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (p : PlF D) (g : Loc.SplitG (M p).L)
    (hsM : (M p).split = some g) (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hge : g.e = sg.e) (hgq : g.q = sg.q) (Z : Formalism.L2.SG.PairVal.MatR D) (c : (D.s.atP p).Ep) :
    p1 sg.e (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z + cornerM p c).det =
      ((sg.q : (D.s.atP p).Fp)⁻¹) ^ (D.R.rS + 1) *
        (Matrix.of (fun a b => cf ⟨δ, M, hA⟩ p a * ((p1 sg.e).comp (D.s.atP p).ιE) (Z a b) * cf ⟨δ, M, hA⟩ p b) +
          cornerF D.R.rS ((((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) + (sg.q : (D.s.atP p).Fp) * p1 sg.e c)).det := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  rw [RingHom.map_det]
  have hX : (p1 sg.e).mapMatrix (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z + cornerM p c) =
      ((sg.q : (D.s.atP p).Fp)⁻¹) •
        (Matrix.of (fun a b => cf ⟨δ, M, hA⟩ p a * ((p1 sg.e).comp (D.s.atP p).ιE) (Z a b) * cf ⟨δ, M, hA⟩ p b) +
          cornerF D.R.rS ((((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) + (sg.q : (D.s.atP p).Fp) * p1 sg.e c)) := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      cornerF, smul_eq_mul]
    have hZZ : Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z a b =
        g.e.symm ((g.e (Formalism.L2.SG.CntLocal.ZhatLoc M δ p Z a b)).1 / (g.q : (D.s.atP p).Fp),
          -((g.e (Formalism.L2.SG.CntLocal.ZhatLoc M δ p Z b a)).2 / (g.q : (D.s.atP p).Fp))) -
        (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
          g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
            (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)) else 0) := by
      simp only [Formalism.L2.SG.CntLocal.ZZP, Loc.HermSp.ZZplusOf, hsM, Matrix.of_apply]
    have hp1Z : p1 sg.e (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z a b) =
        cf ⟨δ, M, hA⟩ p b * cf ⟨δ, M, hA⟩ p a * ((p1 sg.e).comp (D.s.atP p).ιE) (Z a b) / (sg.q : (D.s.atP p).Fp) -
          (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
            -(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) := by
      rw [hZZ, map_sub, hge, hgq, fst_proj_symm, zhatLoc_eq hA p Z a b, ← adeleInfiniteComponent_apply, map_mul, fst_proj_algebraMap]
      split_ifs with h
      · rw [fst_proj_symm]; rfl
      · rw [map_zero]; rfl
    have hp1c : p1 sg.e (cornerM p c a b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then p1 sg.e c else 0 := by
      simp only [cornerM, Matrix.of_apply]
      split_ifs
      · rfl
      · exact map_zero _
    rw [map_add, hp1Z, hp1c]
    split_ifs
    · field_simp
      ring
    · field_simp
      ring
  rw [hX, Matrix.det_smul, Fintype.card_fin]

end DetG2

end Formalism.L2.SG.Pf.ThSomePf

namespace Formalism.L2.SG.Pf.ThSomePf

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.LocUnramB
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section DetG3

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem secondProj_det_corner (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (p : PlF D) (g : Loc.SplitG (M p).L)
    (hsM : (M p).split = some g) (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hge : g.e = sg.e) (hgq : g.q = sg.q) (Z : Formalism.L2.SG.PairVal.MatR D) (c : (D.s.atP p).Ep) :
    p2 sg.e (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z + cornerM p c).det =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) ^ (D.R.rS + 1) *
        (Matrix.of (fun a b => cf ⟨δ, M, hA⟩ p a * ((p2 sg.e).comp (D.s.atP p).ιE) (Z b a) * cf ⟨δ, M, hA⟩ p b) +
          cornerF D.R.rS ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) - (sg.q : (D.s.atP p).Fp) * p2 sg.e c)).det := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  rw [RingHom.map_det]
  have hX : (p2 sg.e).mapMatrix (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z + cornerM p c) =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) •
        (Matrix.of (fun a b => cf ⟨δ, M, hA⟩ p a * ((p2 sg.e).comp (D.s.atP p).ιE) (Z b a) * cf ⟨δ, M, hA⟩ p b) +
          cornerF D.R.rS ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) - (sg.q : (D.s.atP p).Fp) * p2 sg.e c)) := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      cornerF, smul_eq_mul]
    have hZZ : Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z a b =
        g.e.symm ((g.e (Formalism.L2.SG.CntLocal.ZhatLoc M δ p Z a b)).1 / (g.q : (D.s.atP p).Fp),
          -((g.e (Formalism.L2.SG.CntLocal.ZhatLoc M δ p Z b a)).2 / (g.q : (D.s.atP p).Fp))) -
        (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
          g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
            (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)) else 0) := by
      simp only [Formalism.L2.SG.CntLocal.ZZP, Loc.HermSp.ZZplusOf, hsM, Matrix.of_apply]
    have hp2Z : p2 sg.e (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z a b) =
        -(cf ⟨δ, M, hA⟩ p a * cf ⟨δ, M, hA⟩ p b * ((p2 sg.e).comp (D.s.atP p).ιE) (Z b a) /
          (sg.q : (D.s.atP p).Fp)) -
          (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
            (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) := by
      rw [hZZ, map_sub, hge, hgq, snd_proj_symm, zhatLoc_eq hA p Z b a, ← adele_ext_components, map_mul, snd_proj_algebraMap]
      split_ifs with h
      · rw [snd_proj_symm]; rfl
      · rw [map_zero]; rfl
    have hp2c : p2 sg.e (cornerM p c a b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then p2 sg.e c else 0 := by
      simp only [cornerM, Matrix.of_apply]
      split_ifs
      · rfl
      · exact map_zero _
    rw [map_add, hp2Z, hp2c]
    split_ifs
    · field_simp
      ring
    · field_simp
      ring
  rw [hX, Matrix.det_smul, Fintype.card_fin]

theorem blkMod_comps (p : PlF D) (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hsD : (D.s.atP p).split = some sg) (T T' : ℕ) (ζ : D.host.E) :
    p1 sg.e (blkMod δ T T' p (D.R.rS + 1) 1 ζ) =
        (p1 sg.e ((D.s.atP p).ιE ζ) + (T : (D.s.atP p).Fp)) * (sg.q : (D.s.atP p).Fp)⁻¹ ∧
      p2 sg.e (blkMod δ T T' p (D.R.rS + 1) 1 ζ) =
        -(p2 sg.e ((D.s.atP p).ιE ζ) + (T' : (D.s.atP p).Fp)) * (sg.q : (D.s.atP p).Fp)⁻¹ := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  haveI : Nontrivial (D.s.atP p).Ep := PI.ProdFormulaE.Base.nontrivial (D.s.atP p)
  obtain ⟨hi1, hi2⟩ := proj_inverse_algebraMap sg.e (sg.q : (D.s.atP p).Fp) hq
  have hnu : nu D.R.rS (D.R.rS + 1) (D.R.rS + 1 + 1 - 1) = 0 := by unfold nu; omega
  have hc : (D.R.rS + 1 + 1 - 1 = D.R.rS + 1 ∧ (1 : ℕ) = 1) := ⟨by omega, rfl⟩
  simp only [blkMod, tMod, if_pos hc, hnu, pow_zero, Ring.inverse_one, one_mul, twist, qE, tau0, hsD]
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_mul, if_pos (show D.R.rS + 1 + 1 - 1 = D.R.rS + 1 ∧ True from ⟨by omega, trivial⟩), map_mul,
      fst_proj_symm, fst_proj_symm, hi1, adeleInfiniteComponent_apply]
    ring
  · rw [map_sub, map_mul, if_pos (show D.R.rS + 1 + 1 - 1 = D.R.rS + 1 ∧ True from ⟨by omega, trivial⟩), map_mul,
      snd_proj_symm, snd_proj_symm, hi2, adele_ext_components]
    ring

theorem exists_k {K : Type} [Field K] [CharZero K] (a b : K) :
    ∃ k : Fin 3, a + ((k : ℕ) : K) ≠ 0 ∧ b + ((k : ℕ) : K) ≠ 0 := by
  by_cases h0 : a ≠ 0 ∧ b ≠ 0
  · exact ⟨0, by simpa using h0⟩
  by_cases h1 : a + 1 ≠ 0 ∧ b + 1 ≠ 0
  · exact ⟨1, by simpa using h1⟩
  refine ⟨2, ?_⟩
  simp only [Fin.val_two, Nat.cast_ofNat]
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  rw [not_and_or, not_ne_iff, not_ne_iff] at h0 h1
  constructor
  · intro ha
    rcases h0 with h0 | h0
    · rw [h0] at ha; simp at ha
    · rcases h1 with h1 | h1
      · have : (1 : K) = 0 := by linear_combination ha - h1
        exact one_ne_zero this
      · have : (1 : K) = 0 := by linear_combination h1 - h0
        exact one_ne_zero this
  · intro hb
    rcases h0 with h0 | h0
    · rcases h1 with h1 | h1
      · have : (1 : K) = 0 := by linear_combination h1 - h0
        exact one_ne_zero this
      · have : (1 : K) = 0 := by linear_combination hb - h1
        exact one_ne_zero this
    · rw [h0] at hb; simp at hb

end DetG3

end Formalism.L2.SG.Pf.ThSomePf

namespace Formalism.L2.SG.Pf.ThSomePf

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.LocUnramB Formalism.L2.SG.TermLoc
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section DetG4

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem leadMinor_top (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    leadMinorE Z (D.R.rS + 1) = Z.det := by
  unfold leadMinorE; rw [dif_pos le_rfl]; rfl

theorem leadMinor_r (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    leadMinorE Z D.R.rS = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE; rw [dif_pos (Nat.le_succ _)]; rfl

set_option maxHeartbeats 1600000 in

theorem detG (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (p : PlF D) (g : Loc.SplitG (M p).L)
    (hsM : (M p).split = some g) {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} (w : Point D.host.E (D.R.rS + 1))
    (hc : IsInCell (ZhatOM (ZhatL (lf D F0) F')) w) :
    IsUnit (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') +
      cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)).det := by
  have hsp := (hA p).2.2.2.2.2
  rw [hsM] at hsp
  rcases hsD : (D.s.atP p).split with _ | sg
  · rw [hsD] at hsp; exact hsp.elim
  rw [hsD] at hsp
  obtain ⟨hge, hgq⟩ := hsp
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  haveI := (D.s.atP p).char0
  haveI : Nontrivial (D.s.atP p).Ep := PI.ProdFormulaE.Base.nontrivial (D.s.atP p)
  have key : ∀ y : (D.s.atP p).Ep, p1 sg.e y ≠ 0 → p2 sg.e y ≠ 0 → IsUnit y := fun y h1 h2 => by
    have hu : IsUnit (sg.e y) := Prod.isUnit_iff.2 ⟨isUnit_iff_ne_zero.2 h1, isUnit_iff_ne_zero.2 h2⟩
    have := hu.map sg.e.symm
    rwa [AlgEquiv.symm_apply_apply] at this

  have hr := Formalism.L2.SG.Pf.ScalKindPf.dmin_eq hc D.R.rS (Nat.le_succ _)
  have hr1 := Formalism.L2.SG.Pf.ScalKindPf.dmin_eq hc (D.R.rS + 1) le_rfl
  rw [Formalism.L2.SG.Pf.ScalKindPf.sgnL_succ] at hr1
  rw [leadMinor_r] at hr
  rw [leadMinor_top] at hr1
  generalize ZhatL (lf D F0) F' = Z at hr hr1 ⊢
  have hs := Formalism.L2.SG.Pf.ScalKindPf.sgnL_ne (D := D) D.R.rS
  have hpt : Dmin w (D.R.rS + 1) ≠ 0 := by
    rw [Formalism.L2.SG.Pf.dmin_top]; exact Formalism.MainNotions.BridgeLemma.ptMat_det_ne w
  have hdetZ : Z.det ≠ 0 := fun h => hpt (by rw [hr1, h, mul_zero])

  have hcfl : cf (⟨δ, M, hA⟩ : LocDat D) p (Fin.last D.R.rS) = 1 := by simp [cf]
  set P := ∏ a : Fin D.R.rS, cf (⟨δ, M, hA⟩ : LocDat D) p (Fin.castSucc a) with hPdef
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => by
    simp only [cf]; exact pow_ne_zero _ (inv_ne_zero (yP_ne _ p))

  have v1 : ∀ c : (D.s.atP p).Ep,
      p1 sg.e (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z + cornerM p c).det =
        ((sg.q : (D.s.atP p).Fp)⁻¹) ^ (D.R.rS + 1) * (P ^ 2 * (((p1 sg.e).comp (D.s.atP p).ιE) Z.det +
          ((((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) + (sg.q : (D.s.atP p).Fp) * p1 sg.e c) *
            ((p1 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det)) := by
    intro c
    rw [firstProj_det_corner hA u u' p g hsM sg hge hgq Z c]
    have h := det_diag_mul (cf (⟨δ, M, hA⟩ : LocDat D) p) (Z.map ((p1 sg.e).comp (D.s.atP p).ιE))
      ((((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) + (sg.q : (D.s.atP p).Fp) * p1 sg.e c)
    simp only [Matrix.map_apply] at h
    have hd1 : (Z.map ((p1 sg.e).comp (D.s.atP p).ιE)).det = ((p1 sg.e).comp (D.s.atP p).ιE) Z.det := (RingHom.map_det ((p1 sg.e).comp (D.s.atP p).ιE) Z).symm
    have hd1s : ((Z.map ((p1 sg.e).comp (D.s.atP p).ιE)).submatrix Fin.castSucc Fin.castSucc).det = ((p1 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det :=
      (RingHom.map_det ((p1 sg.e).comp (D.s.atP p).ιE) _).symm
    rw [h, hcfl, hd1, hd1s, ← hPdef]
    ring
  have v2 : ∀ c : (D.s.atP p).Ep,
      p2 sg.e (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z + cornerM p c).det =
        (-(sg.q : (D.s.atP p).Fp)⁻¹) ^ (D.R.rS + 1) * (P ^ 2 * (((p2 sg.e).comp (D.s.atP p).ιE) Z.det +
          ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) - (sg.q : (D.s.atP p).Fp) * p2 sg.e c) *
            ((p2 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det)) := by
    intro c
    rw [secondProj_det_corner hA u u' p g hsM sg hge hgq Z c]
    have h := det_diag_mul (cf (⟨δ, M, hA⟩ : LocDat D) p) (Z.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose
      ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) - (sg.q : (D.s.atP p).Fp) * p2 sg.e c)
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h
    have hd2 : (Z.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose.det = ((p2 sg.e).comp (D.s.atP p).ιE) Z.det := by
      rw [Matrix.det_transpose]; exact (RingHom.map_det ((p2 sg.e).comp (D.s.atP p).ιE) Z).symm
    have hd2s : ((Z.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose.submatrix Fin.castSucc Fin.castSucc).det =
        ((p2 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [← Matrix.transpose_submatrix, Matrix.det_transpose]; exact (RingHom.map_det ((p2 sg.e).comp (D.s.atP p).ιE) _).symm
    rw [h, hcfl, hd2, hd2s, ← hPdef]
    ring
  have hqi : ((sg.q : (D.s.atP p).Fp)⁻¹) ^ (D.R.rS + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hq)
  have hqi' : (-(sg.q : (D.s.atP p).Fp)⁻¹) ^ (D.R.rS + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq))
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ hP
  by_cases hD : Dmin w D.R.rS = 0
  · have hcs : cornerSh δ (D.mem u).A.T (D.mem u').A.T p w = 0 := by unfold cornerSh; rw [if_pos hD]
    have hDr : (Z.submatrix Fin.castSucc Fin.castSucc).det = 0 := by
      rw [hr] at hD; exact (mul_eq_zero.1 hD).resolve_left hs
    rw [hcs]
    refine key _ ?_ ?_
    · rw [v1, hDr]
      simp only [map_zero, mul_zero, add_zero]
      exact mul_ne_zero hqi (mul_ne_zero hP2 ((map_ne_zero ((p1 sg.e).comp (D.s.atP p).ιE)).2 hdetZ))
    · rw [v2, hDr]
      simp only [map_zero, mul_zero, add_zero]
      exact mul_ne_zero hqi' (mul_ne_zero hP2 ((map_ne_zero ((p2 sg.e).comp (D.s.atP p).ιE)).2 hdetZ))
  · have hDr : (Z.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := fun h => hD (by rw [hr, h, mul_zero])
    have hζZ : Z.det = zetaOf w * (Z.submatrix Fin.castSucc Fin.castSucc).det := by
      unfold zetaOf
      rw [hr1, hr, mul_div_mul_left _ _ hs, div_mul_cancel₀ _ hDr]
    obtain ⟨b1, b2⟩ := blkMod_comps (δ := δ) p sg hsD (D.mem u).A.T (D.mem u').A.T (zetaOf w)
    obtain ⟨k, hk1, hk2⟩ := exists_k (p1 sg.e (blkMod δ (D.mem u).A.T (D.mem u').A.T p (D.R.rS + 1) 1 (zetaOf w)))
      (p2 sg.e (blkMod δ (D.mem u).A.T (D.mem u').A.T p (D.R.rS + 1) 1 (zetaOf w)))
    have hex : ∃ k : Fin 3, IsUnit (blkMod δ (D.mem u).A.T (D.mem u').A.T p (D.R.rS + 1) 1 (zetaOf w) +
        (((k : Fin 3) : ℕ) : (D.s.atP p).Ep)) := by
      refine ⟨k, key _ ?_ ?_⟩
      · rw [map_add (p1 sg.e), map_natCast (p1 sg.e)]; exact hk1
      · rw [map_add (p2 sg.e), map_natCast (p2 sg.e)]; exact hk2
    have hcs : cornerSh δ (D.mem u).A.T (D.mem u').A.T p w = (((hex.choose : Fin 3) : ℕ) : (D.s.atP p).Ep) := by
      unfold cornerSh nSh; rw [if_neg hD, dif_pos hex]
    have hu := hex.choose_spec
    have hu1 : p1 sg.e (blkMod δ (D.mem u).A.T (D.mem u').A.T p (D.R.rS + 1) 1 (zetaOf w) +
        (((hex.choose : Fin 3) : ℕ) : (D.s.atP p).Ep)) ≠ 0 := fun h => by
      have := hu.map (p1 sg.e); rw [h] at this; exact not_isUnit_zero this
    have hu2 : p2 sg.e (blkMod δ (D.mem u).A.T (D.mem u').A.T p (D.R.rS + 1) 1 (zetaOf w) +
        (((hex.choose : Fin 3) : ℕ) : (D.s.atP p).Ep)) ≠ 0 := fun h => by
      have := hu.map (p2 sg.e); rw [h] at this; exact not_isUnit_zero this
    rw [map_add (p1 sg.e), map_natCast (p1 sg.e) ((hex.choose : Fin 3) : ℕ)] at hu1
    rw [map_add (p2 sg.e), map_natCast (p2 sg.e) ((hex.choose : Fin 3) : ℕ)] at hu2
    simp only [b1] at hu1
    simp only [b2] at hu2
    have hqq : (sg.q : (D.s.atP p).Fp) * (sg.q : (D.s.atP p).Fp)⁻¹ = 1 := mul_inv_cancel₀ hq
    have h1' : ((p1 sg.e).comp (D.s.atP p).ιE) Z.det = p1 sg.e ((D.s.atP p).ιE (zetaOf w)) * ((p1 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det := by
      have := congrArg ((p1 sg.e).comp (D.s.atP p).ιE) hζZ
      rw [map_mul] at this
      exact this
    have h2' : ((p2 sg.e).comp (D.s.atP p).ιE) Z.det = p2 sg.e ((D.s.atP p).ιE (zetaOf w)) * ((p2 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det := by
      have := congrArg ((p2 sg.e).comp (D.s.atP p).ιE) hζZ
      rw [map_mul] at this
      exact this
    rw [hcs]
    refine key _ ?_ ?_
    · rw [v1, map_natCast (p1 sg.e) ((hex.choose : Fin 3) : ℕ)]
      refine mul_ne_zero hqi (mul_ne_zero hP2 ?_)
      have e : ((p1 sg.e).comp (D.s.atP p).ιE) Z.det + ((((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) +
          (sg.q : (D.s.atP p).Fp) * (((hex.choose : Fin 3) : ℕ) : (D.s.atP p).Fp)) *
            ((p1 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det =
          (sg.q : (D.s.atP p).Fp) * ((p1 sg.e ((D.s.atP p).ιE (zetaOf w)) + (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp)) *
            (sg.q : (D.s.atP p).Fp)⁻¹ + (((hex.choose : Fin 3) : ℕ) : (D.s.atP p).Fp)) *
            ((p1 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det := by
        linear_combination h1' - ((p1 sg.e ((D.s.atP p).ιE (zetaOf w)) + (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp)) *
          ((p1 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det) * hqq
      rw [e]
      exact mul_ne_zero (mul_ne_zero hq hu1) ((map_ne_zero ((p1 sg.e).comp (D.s.atP p).ιE)).2 hDr)
    · rw [v2, map_natCast (p2 sg.e) ((hex.choose : Fin 3) : ℕ)]
      refine mul_ne_zero hqi' (mul_ne_zero hP2 ?_)
      have e : ((p2 sg.e).comp (D.s.atP p).ιE) Z.det + ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) -
          (sg.q : (D.s.atP p).Fp) * (((hex.choose : Fin 3) : ℕ) : (D.s.atP p).Fp)) *
            ((p2 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det =
          -(sg.q : (D.s.atP p).Fp) * (-(p2 sg.e ((D.s.atP p).ιE (zetaOf w)) + (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp)) *
            (sg.q : (D.s.atP p).Fp)⁻¹ + (((hex.choose : Fin 3) : ℕ) : (D.s.atP p).Fp)) *
            ((p2 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det := by
        linear_combination h2' - ((p2 sg.e ((D.s.atP p).ιE (zetaOf w)) + (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp)) *
          ((p2 sg.e).comp (D.s.atP p).ιE) (Z.submatrix Fin.castSucc Fin.castSucc).det) * hqq
      rw [e]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 hq) hu2) ((map_ne_zero ((p2 sg.e).comp (D.s.atP p).ιE)).2 hDr)

end DetG4

end Formalism.L2.SG.Pf.ThSomePf

namespace Formalism.L2.SG.Pf.ThSomePf

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.LocUnramB Formalism.L2.SG.TermLoc
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Assembly

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem isLo_of_uni' {K : Type} [CommRing K] {n : ℕ} {L : Matrix (Fin n) (Fin n) K} (h : IsLoUni L) : IsLo L :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩

theorem isUp_of_uni' {K : Type} [CommRing K] {n : ℕ} {U : Matrix (Fin n) (Fin n) K} (h : IsUpUni U) : IsUp U :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h b a).1 hab⟩

theorem cornerSh_mem (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) :
    cornerSh δ T T' p w ∈ (M p).R := by
  unfold cornerSh
  split_ifs
  · exact (M p).R.zero_mem
  · exact natCast_mem (M p).R _

theorem thSome_of (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hNR : NormRepElig u u' F0 what₂)
    (hInt : ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
      ∀ p a b, Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (zT γ) a b ∈ (M p).R) :
    ThSome M δ u u' F0 what₂ := by
  intro γ w hγ p
  have hex := hNR γ w hγ
  have hn : nrep γ = some hex.choose := dif_pos hex
  obtain ⟨-, -, hL, hU, e⟩ := hex.choose_spec
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by unfold zT; rw [hn]
  have hpt : ptT γ = hex.choose.1 := by unfold ptT; rw [hn]
  have hc : IsInCell (ZhatOM (ZhatL (lf D F0) hex.choose.2.1)) hex.choose.1 := ⟨_, _, hL, hU, e⟩
  have hint : ∀ a b, (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (zT γ) +
      cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p hex.choose.1)) a b ∈ (M p).R := fun a b => by
    rw [Matrix.add_apply]
    refine (M p).R.add_mem (hInt γ w hγ p a b) ?_
    simp only [cornerM, Matrix.of_apply]
    split_ifs
    · exact cornerSh_mem _ _ p _
    · exact (M p).R.zero_mem
  have hdet : IsUnit (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (zT γ) +
      cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p hex.choose.1)).det := by
    rw [hz]
    rcases hsM : (M p).split with _ | g
    · exact detL hA u u' p hsM hex.choose.1 _ _ _ (isLo_of_uni' hL) (isUp_of_uni' hU)
        (by rw [← zhatOM_eq]; exact e)
    · exact detG hA u u' p g hsM hex.choose.1 hc
  show thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (zT γ)) ≠ none
  rw [hpt]
  unfold thL clsOf
  rw [dif_pos ⟨hint, hdet⟩]
  exact Option.some_ne_none _

end Assembly

end Formalism.L2.SG.Pf.ThSomePf

namespace Formalism.L2.SG.Pf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem thSome_holds_of {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hNR : NormRepElig u u' F0 what₂)
    (hInt : ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
      ∀ p a b, Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (zT γ) a b ∈ (M p).R) :
    ThSome M δ u u' F0 what₂ :=
  ThSomePf.thSome_of hA hNR hInt

end Formalism.L2.SG.Pf
