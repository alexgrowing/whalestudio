import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhaseL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountLoc

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical ValuativeRel

section CornerSg

variable {K : Type} [Field K] {n : ℕ}

theorem corner_sg (σ : Fin (n + 1) → Fin (n + 1)) (hσ : ∀ a, σ (σ a) = a)
    {L U M : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hL : IsLo L) (hU : IsUp U)
    (hM : ∀ a b, b ≠ σ a → M a b = 0) (c : K) (hu : σ (Fin.last n) ≠ Fin.last n → M (Fin.last n) (σ (Fin.last n)) ≠ 0) :
    ∃ U' : Matrix (Fin (n + 1)) (Fin (n + 1)) K, IsUp U' ∧
      L * M * U - c • Ecorner n = L * (M - (if σ (Fin.last n) = Fin.last n then c else 0) • Ecorner n) * U' ∧
      Formalism.DoubleCosetMeasures.sUp U' = Formalism.DoubleCosetMeasures.sUp U -
        (if σ (Fin.last n) ≠ Fin.last n ∧ (σ (Fin.last n)).val + 1 = n then c / M (Fin.last n) (σ (Fin.last n)) else 0) := by
  classical
  have hLE : L * Ecorner n = Ecorner n := by
    ext a b
    by_cases hb : b = Fin.last n
    · subst hb
      by_cases ha : a = Fin.last n
      · subst ha; simp [Matrix.mul_apply, Ecorner, hL.1]
      · simp [Matrix.mul_apply, Ecorner, ha, hL.2 a (Fin.last n) (Fin.lt_last_iff_ne_last.mpr ha)]
    · simp [Matrix.mul_apply, Ecorner, hb]
  by_cases hl : σ (Fin.last n) = Fin.last n
  · have hEU : Ecorner n * U = Ecorner n := by
      ext a b
      by_cases ha : a = Fin.last n
      · subst ha
        by_cases hb : b = Fin.last n
        · subst hb; simp [Matrix.mul_apply, Ecorner, hU.1]
        · simp [Matrix.mul_apply, Ecorner, hb, hU.2 b (Fin.last n) (Fin.lt_last_iff_ne_last.mpr hb)]
      · simp [Matrix.mul_apply, Ecorner, ha]
    refine ⟨U, hU, ?_, ?_⟩
    · rw [if_pos hl, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, hLE, Matrix.smul_mul, hEU]
    · simp [hl]
  · generalize hj : σ (Fin.last n) = j₀ at hl hu ⊢
    have hm : M (Fin.last n) j₀ ≠ 0 := hu hl
    set X : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
      Matrix.of fun a b => if a = j₀ ∧ b = Fin.last n then c / M (Fin.last n) j₀ else 0 with hX
    have hMX : M * X = c • Ecorner n := by
      ext a b
      by_cases hb : b = Fin.last n
      · subst hb
        by_cases ha : a = Fin.last n
        · subst ha
          simp [Matrix.mul_apply, hX, Ecorner]
          try field_simp
        · have hne : j₀ ≠ σ a := by
            intro h
            apply ha
            have h' := congrArg σ h
            rw [hσ a, ← hj, hσ] at h'
            exact h'.symm
          simp [Matrix.mul_apply, hX, Ecorner, ha, hM a j₀ hne]
      · simp [Matrix.mul_apply, hX, Ecorner, hb]
    refine ⟨U - X, ⟨fun a => ?_, fun a b hab => ?_⟩, ?_, ?_⟩
    · have hn : ¬ (a = j₀ ∧ a = Fin.last n) := fun h => hl (h.1.symm.trans h.2)
      simp only [Matrix.sub_apply, hX, Matrix.of_apply, hU.1 a, if_neg hn, sub_zero]
    · have hn : ¬ (b = j₀ ∧ a = Fin.last n) := fun h => by
        rw [h.2] at hab
        exact absurd hab (not_lt.mpr (Fin.le_last b))
      simp only [Matrix.sub_apply, hX, Matrix.of_apply, hU.2 a b hab, if_neg hn, sub_zero]
    · rw [if_neg hl, zero_smul, sub_zero, Matrix.mul_sub, Matrix.mul_assoc L M X, hMX,
        Matrix.mul_smul, hLE]
    · have key : ∀ j : Fin (n + 1), (if h : j.val + 1 < n + 1 then (U - X) j ⟨j.val + 1, h⟩ else 0) =
          (if h : j.val + 1 < n + 1 then U j ⟨j.val + 1, h⟩ else 0) -
            (if j = j₀ ∧ j.val + 1 = n then c / M (Fin.last n) j₀ else 0) := by
        intro j
        by_cases h1 : j.val + 1 < n + 1
        · rw [dif_pos h1, dif_pos h1, Matrix.sub_apply]
          congr 1
          simp only [hX, Matrix.of_apply, Fin.ext_iff, Fin.val_last]
        · rw [dif_neg h1, dif_neg h1]
          have hn : ¬ (j = j₀ ∧ j.val + 1 = n) := fun h => h1 (by omega)
          rw [if_neg hn, sub_zero]
      unfold Formalism.DoubleCosetMeasures.sUp
      simp only [key, Finset.sum_sub_distrib]
      congr 1
      simp [ite_and, hl]

end CornerSg

section LastBlock

variable {K : Type*} [Zero K]

theorem last_row : ∀ (bs : List (K × ℕ)) (N : ℕ), (∀ b ∈ bs, 1 ≤ b.2) → (bs.map Prod.snd).sum = N + 1 →
    bs.getLast? = some (pTau bs N, pSz bs N) ∧ pSt bs N + pSz bs N = N + 1 ∧ pSig bs N = pSt bs N
  | [], N, _, h => by simp at h
  | (t, s) :: bs, N, hpos, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hlt : N < s
    · have hs : s = N + 1 := by
        have := hpos (t, s) List.mem_cons_self
        have h0 : (bs.map Prod.snd).sum = 0 := by omega
        omega
      have hbs : bs = [] := by
        rcases bs with _ | ⟨b, bs'⟩
        · rfl
        · exfalso
          have hb := hpos b (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [List.map_cons, List.sum_cons] at h
          omega
      subst hbs
      simp only [pTau, pSz, pSt, pSig, if_pos hlt, List.getLast?_singleton]
      refine ⟨trivial, by omega, by omega⟩
    · have hge : s ≤ N := by omega
      have hpos' : ∀ b ∈ bs, 1 ≤ b.2 := fun b hb => hpos b (List.mem_cons_of_mem _ hb)
      have hsum : (bs.map Prod.snd).sum = (N - s) + 1 := by
        have := hpos (t, s) List.mem_cons_self; omega
      obtain ⟨ih1, ih2, ih3⟩ := last_row bs (N - s) hpos' hsum
      have hne : bs ≠ [] := by rintro rfl; simp at hsum
      simp only [pTau, pSz, pSt, pSig, if_neg hlt]
      refine ⟨?_, by omega, by rw [ih3]⟩
      rw [List.getLast?_cons, ih1]
      simp

end LastBlock

section Signs

variable {R : Type} [CommRing R] {r : ℕ}

theorem sLow_sgT (A : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Formalism.DoubleCosetMeasures.sLow (Sg R r * A.transpose * Sg R r) = -Formalism.DoubleCosetMeasures.sUp A := by
  unfold Formalism.DoubleCosetMeasures.sLow Formalism.DoubleCosetMeasures.sUp
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j.val + 1 < r + 1
  · rw [dif_pos h, dif_pos h]
    simp only [Sg, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
    have e : r - j.val = (r - (j.val + 1)) + 1 := by omega
    have hx : (-1 : R) ^ (r - (j.val + 1)) * (-1 : R) ^ (r - (j.val + 1)) = 1 := by
      rw [← mul_pow]; simp
    rw [e, pow_succ]
    linear_combination (-(A j ⟨j.val + 1, h⟩)) * hx
  · rw [dif_neg h, dif_neg h, neg_zero]

theorem sUp_sgT (A : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Formalism.DoubleCosetMeasures.sUp (Sg R r * A.transpose * Sg R r) = -Formalism.DoubleCosetMeasures.sLow A := by
  unfold Formalism.DoubleCosetMeasures.sLow Formalism.DoubleCosetMeasures.sUp
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j.val + 1 < r + 1
  · rw [dif_pos h, dif_pos h]
    simp only [Sg, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
    have e : r - j.val = (r - (j.val + 1)) + 1 := by omega
    have hx : (-1 : R) ^ (r - (j.val + 1)) * (-1 : R) ^ (r - (j.val + 1)) = 1 := by
      rw [← mul_pow]; simp
    rw [e, pow_succ]
    linear_combination (-(A ⟨j.val + 1, h⟩ j)) * hx
  · rw [dif_neg h, dif_neg h, neg_zero]

end Signs

section ModeG

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

set_option maxHeartbeats 2000000 in

theorem local_phase_typed_places (hA : ∀ p, Agree δ M p) : PhaseLocG M δ u u' F0 what₂ := by
  intro γ w F' L U hrel hgen hN p hMp
  obtain ⟨-, -, hLu, hUu, e⟩ := hN
  have hL' := PCount.isLo_of_uni hLu
  have hU' := PCount.isUp_of_uni hUu
  have hf' : ZhatL (lf D F0) F' * Sg D.host.E D.R.rS = L * ptMat w * U := by rw [← zhatOM_eq]; exact e
  obtain ⟨g, hM⟩ := Option.ne_none_iff_exists'.1 hMp
  have hAg := (hA p).2.2.2.2.2
  rcases hR : (D.s.atP p).split with _ | sg
  · simp only [hM, hR] at hAg
  simp only [hM, hR] at hAg
  obtain ⟨hge, hgq⟩ := hAg
  set Zd : LocDat D := ⟨δ, M, hA⟩ with hZd
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  have hcc : ∀ a, cf Zd p a * cfi Zd p a = 1 := cf_cfi Zd p
  have hcc' : ∀ a, cfi Zd p a * cf Zd p a = 1 := cfi_cf Zd p

  have hY1 : (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p).map (p1 sg.e) =
      (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) *
        ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map φ1 * Matrix.diagonal (cf Zd p))) *
        (Matrix.diagonal (cfi Zd p) * U.map φ1 * Matrix.diagonal (cf Zd p)) -
      (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
    rw [PCount.zz1' Zd p sg hR g hM hge hgq u u' (ZhatL (lf D F0) F'), hf', Matrix.map_mul, Matrix.map_mul,
      fact1 (cf Zd p) (cfi Zd p) hcc']

  have e2 : ((ZhatL (lf D F0) F').map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS =
      (Sg (D.s.atP p).Fp D.R.rS * (U.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map φ2 * Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (L.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
    have hA' : ZhatL (lf D F0) F' = L * ptMat w * U * Sg D.host.E D.R.rS := by
      rw [← hf', Matrix.mul_assoc, sg_sq, Matrix.mul_one]
    rw [hA', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
    exact fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])
  have hY2 : (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p).map (p2 sg.e) =
      (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (U.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
          Matrix.diagonal (cfi Zd p)) *
        ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) *
          (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map φ2 * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p))) *
        (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (L.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
          Matrix.diagonal (cf Zd p)) -
      ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
    rw [PCount.zz2' Zd p sg hR g hM hge hgq u u' (ZhatL (lf D F0) F'), e2, fact1 (cf Zd p) (cfi Zd p) hcc']
  have hm1 := PCount.mm1' Zd p sg hR g hM hge hgq (D.mem u).A.T (D.mem u').A.T w
  have hm2 := PCount.mm2' Zd p sg hR g hM hge hgq (D.mem u).A.T (D.mem u').A.T w
  have hl1 : IsLo (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) :=
    isLo_conj (isLo_map φ1 hL') _ _ hcc
  have hr1 : IsUp (Matrix.diagonal (cfi Zd p) * U.map φ1 * Matrix.diagonal (cf Zd p)) :=
    isUp_conj (isUp_map φ1 hU') _ _ hcc'
  have hl2 : IsLo (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (U.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cfi Zd p)) :=
    isLo_conj (isLo_conj (isLo_transpose (isUp_map φ2 hU')) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc
  have hr2 : IsUp (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (L.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cf Zd p)) :=
    isUp_conj (isUp_conj (isUp_transpose (isLo_map φ2 hL')) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc'
  have hcf0 : ∀ a, cf Zd p a ≠ 0 := fun a h => by have := hcc a; rw [h, zero_mul] at this; exact zero_ne_one this
  have hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0 :=
    fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  obtain ⟨r1', hr1', e1, hs1⟩ := corner_sg (sgF w) (sgF_sgF w) hl1 hr1
    (M := (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map φ1 * Matrix.diagonal (cf Zd p)))
    (fun a b hb => by
      simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb,
        map_zero, mul_zero, zero_mul, smul_eq_mul])
    (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
    (fun _ => by
      simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true,
        smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero hq) (mul_ne_zero (mul_ne_zero (hcf0 _) ((map_ne_zero _).2 (pTau_ne' _ _))) (hcf0 _)))
  obtain ⟨r2', hr2', e2', hs2⟩ := corner_sg (sgF w) (sgF_sgF w) hl2 hr2
    (M := (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) *
      (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map φ2 * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)))
    (fun a b hb => by
      simp only [Sg, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb,
        map_zero, mul_zero, zero_mul, smul_eq_mul])
    ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
    (fun _ => by
      simp only [Sg, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true,
        smul_eq_mul]
      exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero hq)) (by have hpt := pTau_ne' w (Fin.last D.R.rS); simp only [Fin.val_last] at hpt; simp [hcf0, hpt]))
  have hδZ : Zd.δ = δ := rfl
  have hm1' := hm1
  rw [hδZ, ← hφ1] at hm1'
  have hm2' := hm2
  rw [hδZ, ← hφ2] at hm2'
  have hY : CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p =
      glue sg.e (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p))
          (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (U.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            Matrix.diagonal (cfi Zd p)) *
        modMat δ (D.mem u).A.T (D.mem u').A.T p w * glue sg.e r1' r2' := by
    have c1eq : (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p).map (p1 sg.e) =
        (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) *
          (modMat δ (D.mem u).A.T (D.mem u').A.T p w).map (p1 sg.e) * r1' := by
      rw [hm1']; exact hY1.trans e1
    have c2eq : (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p).map (p2 sg.e) =
        (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (U.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            Matrix.diagonal (cfi Zd p)) *
          (modMat δ (D.mem u).A.T (D.mem u').A.T p w).map (p2 sg.e) * r2' := by
      rw [hm2']; exact hY2.trans e2'
    refine mat_eq sg.e ?_ ?_
    · rw [c1eq]; conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst]
    · rw [c2eq]; conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd]
  obtain ⟨w₀, hw₀⟩ := PCount.modPt_full (δ := δ) (D.mem u).A.T (D.mem u').A.T p (hA p).2.1 w
  rw [phL_of_dec M δ (hA p).1 hw₀ (isLo_glue sg.e hl1 hl2) (isUp_glue sg.e hr1' hr2') hY]
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq]

  have hx1 : p1 sg.e (Formalism.DoubleCosetMeasures.sLow (glue sg.e (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p))
      (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (U.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        Matrix.diagonal (cfi Zd p))) + Formalism.DoubleCosetMeasures.sUp (glue sg.e r1' r2')) =
      Formalism.DoubleCosetMeasures.sLow (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) + Formalism.DoubleCosetMeasures.sUp r1' := by
    rw [map_add, ← sLow_map, ← sUp_map, glue_map_fst, glue_map_fst]
  have hx2 : p2 sg.e (Formalism.DoubleCosetMeasures.sLow (glue sg.e (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p))
      (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (U.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        Matrix.diagonal (cfi Zd p))) + Formalism.DoubleCosetMeasures.sUp (glue sg.e r1' r2')) =
      Formalism.DoubleCosetMeasures.sLow (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (U.map φ2).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        Matrix.diagonal (cfi Zd p)) + Formalism.DoubleCosetMeasures.sUp r2' := by
    rw [map_add, ← sLow_map, ← sUp_map, glue_map_snd, glue_map_snd]

  have hyc : ∀ (j : Fin (D.R.rS + 1)) (h : j.val + 1 < D.R.rS + 1), cf Zd p ⟨j.val + 1, h⟩ * cfi Zd p j = yP Zd p :=
    fun j h => cf_mul_cfi Zd p ⟨j.val + 1, h⟩ j rfl
  have hyc' : ∀ (j : Fin (D.R.rS + 1)) (h : j.val + 1 < D.R.rS + 1), cfi Zd p j * cf Zd p ⟨j.val + 1, h⟩ = yP Zd p :=
    fun j h => by rw [mul_comm]; exact cf_mul_cfi Zd p ⟨j.val + 1, h⟩ j rfl
  have hl1s : Formalism.DoubleCosetMeasures.sLow (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) =
      yP Zd p * φ1 (PairVal.sgLo L) := by
    rw [sLow_conj _ _ _ _ hyc, sLow_map, sgLo_eq]
  have hr1s : Formalism.DoubleCosetMeasures.sUp (Matrix.diagonal (cfi Zd p) * U.map φ1 * Matrix.diagonal (cf Zd p)) =
      yP Zd p * φ1 (PairVal.sgUp U) := by
    rw [sUp_conj _ _ _ _ hyc', sUp_map, sgUp_eq]
  have hl2s : Formalism.DoubleCosetMeasures.sLow (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (U.map φ2).transpose *
      Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p)) = -(yP Zd p * φ2 (PairVal.sgUp U)) := by
    rw [sLow_conj _ _ _ _ hyc, sLow_sgT, sUp_map, sgUp_eq]; ring
  have hr2s : Formalism.DoubleCosetMeasures.sUp (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (L.map φ2).transpose *
      Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) = -(yP Zd p * φ2 (PairVal.sgLo L)) := by
    rw [sUp_conj _ _ _ _ hyc', sUp_sgT, sLow_map, sgLo_eq]; ring

  have hpsiR : ∀ x, (M p).psiR x = g.psiF ((p1 sg.e x - p2 sg.e x) / (sg.q : (D.s.atP p).Fp)) := by
    intro x
    unfold Loc.Model.psiR
    rw [hM]
    show g.psiF ((M p).trR g x) = _
    simp only [Loc.Model.trR, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [hge, hgq]
    rfl

  have hAgr := (hA p).2.2.2.2.1
  set s := PairVal.sgLo L + PairVal.sgUp U with hsdef
  have hgE : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have : 0 < gS D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    exact_mod_cast this.ne'
  have hδ : δ p ≠ 0 := (hA p).2.1
  have htgt : (D.s.atP p).psiE ((D.s.atP p).ιE (-(s / ((gS D : ℕ) : D.host.E)))) =
      g.psiF (δ p * (φ1 s + φ2 s) / ((gS D : ℕ) : (D.s.atP p).Fp)) := by
    have h := hAgr ((D.s.atP p).ιE (s / ((gS D : ℕ) : D.host.E)) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))
    rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hδ, map_one, mul_one, ← map_neg] at h
    rw [← h, g.fractionFieldToGenericStalk_algebraMap_eq, hge, map_mul, AlgEquiv.commutes]
    congr 1
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.algebraMap_apply, RingHom.id_apply]
    rw [← adeleInfiniteComponent_apply, ← adele_ext_components]
    have e1 : p1 sg.e ((D.s.atP p).ιE (s / ((gS D : ℕ) : D.host.E))) = φ1 s / ((gS D : ℕ) : (D.s.atP p).Fp) := by
      show φ1 (s / ((gS D : ℕ) : D.host.E)) = _
      rw [map_div₀, map_natCast]
    have e2 : p2 sg.e ((D.s.atP p).ιE (s / ((gS D : ℕ) : D.host.E))) = φ2 s / ((gS D : ℕ) : (D.s.atP p).Fp) := by
      show φ2 (s / ((gS D : ℕ) : D.host.E)) = _
      rw [map_div₀, map_natCast]
    rw [e1, e2]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    ring

  have hgp : gpart p = Loc.resChar p := by
    have hmem := (D.s_split p).1 (by rw [hR]; rfl)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    unfold gpart
    by_cases h0 : Loc.resChar p = D.host.g 0
    · rw [if_pos h0, h0]
    · rw [if_neg h0, if_pos (hmem.resolve_left h0), hmem.resolve_left h0]
  have hres : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ≠ 0 := by rw [← sg.q_eq]; exact hq
  have hgF : ((gS D : ℕ) : (D.s.atP p).Fp) ≠ 0 := by
    rw [← map_natCast (D.s.atP p).ιF]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos).ne')
  have hu : (D.s.atP p).ιF ((uP p : ℚ) : D.host.F) =
      ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) / ((gS D : ℕ) : (D.s.atP p).Fp) := by
    rw [show ((uP p : ℚ) : D.host.F) = ((gpart p : ℕ) : D.host.F) / ((gS D : ℕ) : D.host.F) by unfold uP; push_cast; ring,
      map_div₀, map_natCast, map_natCast, hgp]
  have hyq : yP Zd p / (sg.q : (D.s.atP p).Fp) = δ p / ((gS D : ℕ) : (D.s.atP p).Fp) := by
    show δ p * (D.s.atP p).ιF ((uP p : ℚ) : D.host.F) / (sg.q : (D.s.atP p).Fp) = _
    rw [hu, sg.q_eq]
    field_simp
  rw [htgt, hpsiR, hx1, hx2, hs1, hs2, hl1s, hr1s, hl2s, hr2s]

  have hpos : ∀ b ∈ w.1, 1 ≤ b.2 := fun b hb => (w.2.1 b hb).2
  obtain ⟨hlast, hst, hsig⟩ := last_row w.1 D.R.rS hpos w.2.2
  have hσv : (sgF w (Fin.last D.R.rS)).val = pSt w.1 D.R.rS := by simp [sgF, hsig]
  have hdf : dfac M δ (D.mem u).A.T (D.mem u').A.T p w = if pSz w.1 D.R.rS = 2 then
      (M p).psiR (tau0 p (D.mem u).A.T (D.mem u').A.T *
        Ring.inverse (blkMod δ (D.mem u).A.T (D.mem u').A.T p D.R.rS 2 (pTau w.1 D.R.rS))) else 1 := by
    unfold dfac
    rw [hR, hlast]
    rcases hs : pSz w.1 D.R.rS with _ | _ | _ | k <;> simp
  have hyP : yP Zd p = δ p / ((gS D : ℕ) : (D.s.atP p).Fp) * (sg.q : (D.s.atP p).Fp) := by
    rw [← hyq]; field_simp
  by_cases h2 : pSz w.1 D.R.rS = 2
  · have hrs : 1 ≤ D.R.rS := by omega
    have hne : sgF w (Fin.last D.R.rS) ≠ Fin.last D.R.rS := fun h => by
      have := congrArg Fin.val h; rw [hσv, Fin.val_last] at this; omega
    have hc : sgF w (Fin.last D.R.rS) ≠ Fin.last D.R.rS ∧ (sgF w (Fin.last D.R.rS)).val + 1 = D.R.rS :=
      ⟨hne, by rw [hσv]; omega⟩
    rw [hdf, if_pos h2, if_pos hc, if_pos hc, hpsiR, ← AddChar.map_add_eq_mul]
    congr 1
    set b := blkMod δ (D.mem u).A.T (D.mem u').A.T p D.R.rS 2 (pTau w.1 D.R.rS) with hb
    have hmb : modMat δ (D.mem u).A.T (D.mem u').A.T p w (Fin.last D.R.rS) (sgF w (Fin.last D.R.rS)) = b := by
      rw [modMat_apply', if_pos rfl, Fin.val_last, h2, show 1 + pSt w.1 D.R.rS = D.R.rS by omega]
    have hX1 : ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map φ1 * Matrix.diagonal (cf Zd p)))
        (Fin.last D.R.rS) (sgF w (Fin.last D.R.rS)) = p1 sg.e b := by
      have h := congrFun (congrFun hm1' (Fin.last D.R.rS)) (sgF w (Fin.last D.R.rS))
      rw [Matrix.map_apply, hmb, if_neg hne, zero_smul, sub_zero] at h
      exact h.symm
    have hX2 : ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) *
        (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map φ2 * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)))
        (Fin.last D.R.rS) (sgF w (Fin.last D.R.rS)) = p2 sg.e b := by
      have h := congrFun (congrFun hm2' (Fin.last D.R.rS)) (sgF w (Fin.last D.R.rS))
      rw [Matrix.map_apply, hmb, if_neg hne, zero_smul, sub_zero] at h
      exact h.symm
    have hb1 : p1 sg.e b ≠ 0 := by
      rw [← hX1]
      simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true,
        smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero hq) (by have hpt := pTau_ne' w (Fin.last D.R.rS); simp only [Fin.val_last] at hpt; simp [hcf0, hpt])
    have hb2 : p2 sg.e b ≠ 0 := by
      rw [← hX2]
      simp only [Sg, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true,
        smul_eq_mul]
      exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero hq)) (by have hpt := pTau_ne' w (Fin.last D.R.rS); simp only [Fin.val_last] at hpt; simp [hcf0, hpt])
    have hbu : IsUnit b := by
      have h : IsUnit (sg.e b) := Prod.isUnit_iff.2 ⟨isUnit_iff_ne_zero.2 hb1, isUnit_iff_ne_zero.2 hb2⟩
      exact (isUnit_map_iff sg.e b).1 h
    have hinv1 : p1 sg.e (Ring.inverse b) = (p1 sg.e b)⁻¹ := by
      have h := congrArg (p1 sg.e) (Ring.inverse_mul_cancel b hbu)
      rw [map_mul, map_one] at h
      exact eq_inv_of_mul_eq_one_left h
    have hinv2 : p2 sg.e (Ring.inverse b) = (p2 sg.e b)⁻¹ := by
      have h := congrArg (p2 sg.e) (Ring.inverse_mul_cancel b hbu)
      rw [map_mul, map_one] at h
      exact eq_inv_of_mul_eq_one_left h
    have hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp)⁻¹ := by
      simp only [qE, hR]
      have := Ring.inverse_unit ((Units.mk0 (sg.q : (D.s.atP p).Fp) hq).map
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
      simpa only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
        Units.val_inv_eq_inv_val] using this
    have ht1 : p1 sg.e (tau0 p (D.mem u).A.T (D.mem u').A.T) =
        -(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) * (sg.q : (D.s.atP p).Fp)⁻¹ := by
      simp only [tau0, hR, map_mul, fst_proj_symm, hqi, fst_proj_algebraMap]
    have ht2 : p2 sg.e (tau0 p (D.mem u).A.T (D.mem u').A.T) =
        (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) * (sg.q : (D.s.atP p).Fp)⁻¹ := by
      simp only [tau0, hR, map_mul, snd_proj_symm, hqi, snd_proj_algebraMap]
    rw [hX1, hX2, map_mul, map_mul, ht1, ht2, hinv1, hinv2, hsdef, map_add, map_add, hyP]
    field_simp
    ring
  · have hc : ¬ (sgF w (Fin.last D.R.rS) ≠ Fin.last D.R.rS ∧ (sgF w (Fin.last D.R.rS)).val + 1 = D.R.rS) := by
      rintro ⟨-, h2'⟩
      apply h2
      rw [hσv] at h2'
      omega
    rw [hdf, if_neg h2, if_neg hc, if_neg hc, one_mul]
    congr 1
    rw [hsdef, map_add, map_add, hyP]
    field_simp
    ring

end ModeG

end Formalism.L2.SG.Pf.Coef
