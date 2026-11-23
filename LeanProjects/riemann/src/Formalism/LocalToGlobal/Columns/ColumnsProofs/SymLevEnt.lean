import Mathlib
import Formalism.LocalToGlobal.Columns.OcbLevIsSym
import Formalism.LocalToGlobal.Columns.RecLevelSymF

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Fix

variable {κ : Type} [CommRing κ]

theorem sl_HJsym_col_k {n r k t j rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) {M : GL (Fin n) κ}
    (hM : M ∈ HJsym κ n k r t j rS h) (i : Fin n) (hk : k < n) :
    (M : Matrix (Fin n) (Fin n) κ) i ⟨k, hk⟩ = if i.val = k then 1 else 0 := by
  obtain ⟨hB, h0⟩ := mem_HPar.mp hM
  have hkr : k < r := by omega
  by_cases hi : i.val < r
  · obtain ⟨h1, h2, h3⟩ := (mem_HPsymF_iff (show k + rS ≤ r by omega)).mp h0
    have e : ∀ a b : Fin r, ((blk0 n κ h (List.replicate j t) ⟨M, hB⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b =
        (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) := fun a b => rfl
    have ei : i = Fin.castLE h ⟨i.val, hi⟩ := Fin.ext rfl
    have ek : (⟨k, hk⟩ : Fin n) = Fin.castLE h ⟨k, hkr⟩ := Fin.ext rfl
    rw [ei, ek, ← e]
    by_cases hik : i.val = k
    · rw [if_pos (by simpa using hik)]
      have : (⟨i.val, hi⟩ : Fin r) = ⟨k, hkr⟩ := Fin.ext hik
      rw [this]
      exact h2 _
    · rw [if_neg (by simpa using hik)]
      by_cases hrs : rS = 0
      · subst hrs
        by_cases hik' : i.val < k
        · exact h3 ⟨i.val, hi⟩ ⟨k, hkr⟩ hik' (by simp)
        · apply h1
          simp only [symIdx]
          split_ifs <;> omega
      · apply h1
        simp only [symIdx]
        split_ifs <;> omega
  · rw [if_neg (by omega)]
    apply hB
    show coarse r (List.replicate j t) k < coarse r (List.replicate j t) i.val
    rw [coarse_of_lt hkr, coarse_of_le (by omega)]
    omega

end Fix

theorem lastLevel_fixes_basisVector_holds : FixESym := by
  intro X Pr R Ch m2 hm h hh w
  have hj : m2 + 1 + 1 = R.m := by omega
  have hw : h w ∈ (colLevSym Ch (m2 + 1) w).H := LevFam.mem_at _ ⟨h, hh⟩ w
  rw [colLevSym_pred Ch hj] at hw
  have hk : R.k < R.N (m2 + 1) := by
    have := r_le_N_of_le (R := R) hj.ge
    have := r_eq_sym R
    omega
  funext i
  show ∑ l, ((h w : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) : Matrix _ _ (𝓞 X.E ⧸ w.1.asIdeal)) i l *
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k l = Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k i
  rw [Finset.sum_eq_single ⟨R.k, hk⟩]
  · rw [sl_HJsym_col_k (r_le_N_of_le (R := R) hj.ge) (r_eq_sym R) hw i hk]
    simp [Loc.eN]
  · intro l _ hl
    have : l.val ≠ R.k := fun e => hl (Fin.ext e)
    simp [Loc.eN, this]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

section EntY

variable {κ : Type} [CommRing κ]

def slAllowY (k rS r t P P' : ℕ) : Prop :=
  if P' < r then P < r ∧ ¬ symIdx k rS P' < symIdx k rS P ∧ ¬ (P < k ∧ P' = k + rS)
  else P < r ∨ (P - r) / t ≤ (P' - r) / t

theorem sl_mem_HJsym_iff {n r k t j rS : ℕ} (h : r ≤ n) (hkr : k + rS ≤ r) (ht : 0 < t) (hn : n ≤ r + j * t)
    (M : GL (Fin n) κ) :
    M ∈ HJsym κ n k r t j rS h ↔ (∀ P : Fin n, P.val < r → (M : Matrix (Fin n) (Fin n) κ) P P = 1) ∧
      ∀ P P' : Fin n, P ≠ P' → (M : Matrix (Fin n) (Fin n) κ) P P' ≠ 0 → slAllowY k rS r t P.val P'.val := by
  have hc : ∀ x : Fin n, coarse r (List.replicate j t) x.val = if x.val < r then 0 else (x.val - r) / t + 1 :=
    fun x => coarse_rep ht (by omega)
  constructor
  · intro hM
    obtain ⟨hB, h0⟩ := mem_HPar.mp hM
    obtain ⟨h1, h2, h3⟩ := (mem_HPsymF_iff hkr).mp h0
    have e : ∀ a b : Fin r, ((blk0 n κ h (List.replicate j t) ⟨M, hB⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b =
        (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) := fun a b => rfl
    have hlow : ∀ P P' : Fin n, P'.val < r → ¬ P.val < r → (M : Matrix (Fin n) (Fin n) κ) P P' = 0 := by
      intro P P' hP' hP
      apply hB
      show coarse r (List.replicate j t) P'.val < coarse r (List.replicate j t) P.val
      rw [hc, hc, if_pos hP', if_neg hP]
      exact Nat.succ_pos _
    refine ⟨fun P hP => ?_, fun P P' hne hnz => ?_⟩
    · have := h2 ⟨P.val, hP⟩
      rw [e] at this
      exact this
    · unfold slAllowY
      split_ifs with hP'
      · have hP : P.val < r := by
          by_contra hP
          exact hnz (hlow P P' hP' hP)
        refine ⟨hP, fun hlt => hnz ?_, fun ⟨a, b⟩ => hnz ?_⟩
        · have := h1 ⟨P.val, hP⟩ ⟨P'.val, hP'⟩ hlt
          rw [e] at this
          exact this
        · have := h3 ⟨P.val, hP⟩ ⟨P'.val, hP'⟩ a b
          rw [e] at this
          exact this
      · by_contra hc2
        push Not at hc2
        apply hnz
        apply hB
        show coarse r (List.replicate j t) P'.val < coarse r (List.replicate j t) P.val
        rw [hc, hc, if_neg hP', if_neg (by omega)]
        generalize (P.val - r) / t = A at *
        generalize (P'.val - r) / t = B at *
        omega
  · rintro ⟨hd, ho⟩
    have hB : M ∈ blockUT n κ r (List.replicate j t) := by
      intro P P' hlt
      have hlt' : coarse r (List.replicate j t) P'.val < coarse r (List.replicate j t) P.val := hlt
      by_contra hnz
      have hne : P ≠ P' := fun e => by rw [e] at hlt'; exact lt_irrefl _ hlt'
      have := ho P P' hne hnz
      rw [hc, hc] at hlt'
      unfold slAllowY at this
      generalize (P.val - r) / t = A at *
      generalize (P'.val - r) / t = B at *
      split_ifs at this hlt' <;> omega
    refine mem_HPar.mpr ⟨hB, (mem_HPsymF_iff hkr).mpr ⟨fun a b hab => ?_, fun a => ?_, fun a b ha hb => ?_⟩⟩
    · show (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) = 0
      by_contra hnz
      have hne : Fin.castLE h a ≠ Fin.castLE h b := fun e => by
        have : a = b := Fin.castLE_injective h e
        rw [this] at hab
        exact lt_irrefl _ hab
      have := ho _ _ hne hnz
      unfold slAllowY at this
      rw [if_pos (show (Fin.castLE h b).val < r from b.2)] at this
      exact this.2.1 hab
    · exact hd (Fin.castLE h a) a.2
    · show (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) = 0
      by_contra hnz
      have hne : Fin.castLE h a ≠ Fin.castLE h b := fun e => by
        have := congrArg Fin.val e
        simp only [Fin.val_castLE] at this
        omega
      have := ho _ _ hne hnz
      unfold slAllowY at this
      rw [if_pos (show (Fin.castLE h b).val < r from b.2)] at this
      exact this.2.2 ⟨ha, hb⟩

theorem sl_allow_iff {k rS j t c p p' : ℕ} (hc : c + j = 2 * rS + 1) (hne : p ≠ p') :
    slAllowY k rS (k + j + c) t (if p < k then p else p + c) (if p' < k then p' else p' + c) ↔ ocbXAllow k rS j t p p' := by
  unfold slAllowY ocbXAllow symIdx
  by_cases h1 : p < k <;> by_cases h2 : p' < k <;> simp only [h1, h2, if_true, if_false, Nat.add_sub_add_right] <;>
    generalize (p - (k + j)) / t = A <;> generalize (p' - (k + j)) / t = B <;> split_ifs <;> (try simp only [true_and, false_and, or_false]) <;> omega

end EntY

section InsPat

variable {κ : Type} [CommRing κ]

theorem sl_insEquiv_symm_val {N c k N' : ℕ} (hk : k ≤ N) (hN : N' = N + c) (p : Fin N) :
    ((insEquiv N c k N' hk hN).symm (Sum.inl p)).val = if p.val < k then p.val else p.val + c := rfl

theorem sl_ocbM {N : ℕ} (M : GL (Fin N) κ) (p p' : Fin N) : ocbM M p.val p'.val = (M : Matrix (Fin N) (Fin N) κ) p p' := by
  unfold ocbM
  rw [dif_pos ⟨p.2, p'.2⟩]

theorem sl_insGL_pat {N c k j t rS r N' : ℕ} (hk : k ≤ N) (hN' : N' = N + c) (h : r ≤ N') (hr : r = k + j + c)
    (hNd : N = k + j + j * t) (hc : c + j = 2 * rS + 1) (ht : 0 < t) (M : GL (Fin N) κ) :
    insGL κ N c k N' hk hN' M ∈ HJsym κ N' k r t j rS h ↔ ocbXPat k rS j t M := by
  rw [sl_mem_HJsym_iff h (by omega) ht (by subst hN' hr hNd; omega)]
  have hv : ∀ P : Fin N', ∀ p : Fin N, insEquiv N c k N' hk hN' P = Sum.inl p →
      P.val = if p.val < k then p.val else p.val + c := by
    intro P p hP
    rw [← sl_insEquiv_symm_val hk hN' p, ← hP, Equiv.symm_apply_apply]
  have hq : ∀ P : Fin N', ∀ q : Fin c, insEquiv N c k N' hk hN' P = Sum.inr q → P.val = k + q.val := by
    intro P q hP
    have := congrArg Fin.val ((Equiv.symm_apply_eq _).mpr hP.symm)
    rw [← this]
    rfl
  constructor
  · rintro ⟨hd, ho⟩
    refine ⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩
    · have hpN : p < N := by omega
      have := hd ((insEquiv N c k N' hk hN').symm (Sum.inl ⟨p, hpN⟩))
        (by rw [sl_insEquiv_symm_val]; dsimp only; split_ifs <;> omega)
      rw [insGL_val, Equiv.apply_symm_apply, Matrix.fromBlocks_apply₁₁] at this
      rw [sl_ocbM M ⟨p, hpN⟩ ⟨p, hpN⟩]
      exact this
    · have hne' : (insEquiv N c k N' hk hN').symm (Sum.inl ⟨p, hp⟩) ≠ (insEquiv N c k N' hk hN').symm (Sum.inl ⟨p', hp'⟩) :=
        fun e => hne (congrArg Fin.val (Sum.inl_injective ((insEquiv N c k N' hk hN').symm.injective e)))
      have := ho _ _ hne' (by
        rw [insGL_val, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Matrix.fromBlocks_apply₁₁]
        rw [sl_ocbM M ⟨p, hp⟩ ⟨p', hp'⟩] at hnz
        exact hnz)
      rw [sl_insEquiv_symm_val, sl_insEquiv_symm_val, hr] at this
      exact (sl_allow_iff hc hne).mp this
  · rintro ⟨hd, ho⟩
    refine ⟨fun P hP => ?_, fun P P' hne hnz => ?_⟩
    · rw [insGL_val]
      rcases hP1 : insEquiv N c k N' hk hN' P with p | q
      · rw [Matrix.fromBlocks_apply₁₁]
        have e := hv P p hP1
        have := hd p.val (by split_ifs at e <;> omega)
        rw [sl_ocbM] at this
        exact this
      · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq]
    · rw [insGL_val] at hnz
      rcases hP1 : insEquiv N c k N' hk hN' P with p | q <;> rcases hP2 : insEquiv N c k N' hk hN' P' with p' | q' <;>
        rw [hP1, hP2] at hnz
      · rw [Matrix.fromBlocks_apply₁₁] at hnz
        have hpp : p.val ≠ p'.val := fun e => hne (by
          have : p = p' := Fin.ext e
          rw [← (insEquiv N c k N' hk hN').symm_apply_apply P, ← (insEquiv N c k N' hk hN').symm_apply_apply P', hP1, hP2, this])
        have := ho p.val p'.val p.2 p'.2 hpp (by rw [sl_ocbM]; exact hnz)
        rw [hv P p hP1, hv P' p' hP2, hr]
        exact (sl_allow_iff hc hpp).mpr this
      · rw [Matrix.fromBlocks_apply₁₂] at hnz
        exact absurd rfl hnz
      · rw [Matrix.fromBlocks_apply₂₁] at hnz
        exact absurd rfl hnz
      · rw [Matrix.fromBlocks_apply₂₂] at hnz
        have hqq : q ≠ q' := fun e => hne (by
          rw [← (insEquiv N c k N' hk hN').symm_apply_apply P, ← (insEquiv N c k N' hk hN').symm_apply_apply P', hP1, hP2, e])
        exact absurd (Matrix.one_apply_ne hqq) hnz

end InsPat

section EndPat

variable {κ : Type} [CommRing κ]

theorem mem_level_zero_iff_pattern {n k rS t : ℕ} (hn : n = k) (M : GL (Fin n) κ) : M ∈ HX κ n k t 0 ↔ ocbXPat k rS 0 t M := by
  subst hn
  have hf : ∀ x : Fin n, fine (n + 0) [] x.val = x.val := fun x => fine_self_lt (by omega)
  constructor
  · rintro ⟨hB, hd⟩
    refine ⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩
    · rw [sl_ocbM M ⟨p, by omega⟩ ⟨p, by omega⟩]
      exact hd ⟨p, by omega⟩ hp
    · unfold ocbXAllow
      rw [if_pos (by omega)]
      left
      by_contra hlt
      apply hnz
      rw [sl_ocbM M ⟨p, hp⟩ ⟨p', hp'⟩]
      apply hB
      show fine (n + 0) [] p' < fine (n + 0) [] p
      rw [hf ⟨p', hp'⟩, hf ⟨p, hp⟩]
      show p' < p
      omega
  · rintro ⟨hd, ho⟩
    refine ⟨fun i j hij => ?_, fun i hi => ?_⟩
    · have hij' : fine (n + 0) [] j.val < fine (n + 0) [] i.val := hij
      rw [hf, hf] at hij'
      by_contra hnz
      have := ho i.val j.val i.2 j.2 (fun e => by omega) (by rw [sl_ocbM]; exact hnz)
      unfold ocbXAllow at this
      rw [if_pos (by omega)] at this
      omega
    · have := hd i.val hi
      rw [sl_ocbM] at this
      exact this

theorem sl_HJsym_top_pat {N k j t rS r : ℕ} (h : r ≤ N) (hr : r = k + j) (hNd : N = k + j + j * t) (hc : j = 2 * rS + 1)
    (ht : 0 < t) (M : GL (Fin N) κ) : M ∈ HJsym κ N k r t j rS h ↔ ocbXPat k rS j t M := by
  rw [sl_mem_HJsym_iff h (by omega) ht (by omega)]
  have hsimp : ∀ x, (if x < k then x else x + 0) = x := fun x => by split_ifs <;> rfl
  constructor
  · rintro ⟨hd, ho⟩
    refine ⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩
    · rw [sl_ocbM M ⟨p, by omega⟩ ⟨p, by omega⟩]
      exact hd ⟨p, by omega⟩ (show p < r by omega)
    · have := ho ⟨p, hp⟩ ⟨p', hp'⟩ (fun e => hne (congrArg Fin.val e)) (by rw [← sl_ocbM]; exact hnz)
      have h2 := (sl_allow_iff (k := k) (rS := rS) (j := j) (t := t) (c := 0) (by omega) hne).mp
      rw [hsimp, hsimp, Nat.add_zero, ← hr] at h2
      exact h2 this
  · rintro ⟨hd, ho⟩
    refine ⟨fun P hP => ?_, fun P P' hne hnz => ?_⟩
    · have := hd P.val (by omega)
      rw [sl_ocbM] at this
      exact this
    · have hne' : P.val ≠ P'.val := fun e => hne (Fin.ext e)
      have := ho P.val P'.val P.2 P'.2 hne' (by rw [sl_ocbM]; exact hnz)
      have h2 := (sl_allow_iff (k := k) (rS := rS) (j := j) (t := t) (c := 0) (by omega) hne').mpr this
      rw [hsimp, hsimp, Nat.add_zero, ← hr] at h2
      exact h2

end EndPat

theorem sl_ocbH {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (m2 : ℕ) (hm : R.m = m2 + 2) :
    ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)),
      hbar ∈ (colLevSym Ch j w).H ↔ ocbXPat R.k R.rS j R.t hbar := by
  intro j hj w hbar
  have hr := r_eq_sym R
  have hrm : R.r = R.k + R.m - 1 := rfl
  have hN := N_eq_blocks R j
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [colLevSym_zero]
    show hbar ∈ (colLev Ch 0 w).H ↔ _
    unfold colLev
    rw [if_pos (by omega)]
    exact mem_level_zero_iff_pattern (by simp [Ranks.N]) hbar
  · by_cases htop : j + 1 = R.m
    · rw [colLevSym_pred Ch htop]
      exact sl_HJsym_top_pat _ (by omega) hN (by omega) (t_pos R) hbar
    · have h1 : j + 1 < R.m := by omega
      rw [colLevSym_mid_H Ch (by omega) h1 w, Subgroup.mem_comap]
      exact sl_insGL_pat _ rfl _ (by omega) hN (by omega) (t_pos R) hbar

section LamEnt

variable {κ K : Type} [CommRing κ] [Field K]

theorem sl_supSum_eq {n a : ℕ} (S : Finset ℕ) (A : Matrix (Fin n) (Fin n) κ) :
    supSum a S A = ∑ i ∈ Finset.range n,
      if i + 1 < a ∧ i ∈ S then (if h : i + 1 < n then A ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0) else 0 := by
  unfold supSum
  rw [← Fin.sum_univ_eq_sum_range (fun i => if i + 1 < a ∧ i ∈ S then (if h : i + 1 < n then A ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0)
    else 0) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hc : i.val + 1 < a ∧ i.val ∈ S
  · rw [if_pos hc]
    by_cases hi1 : i.val + 1 < n
    · rw [dif_pos hi1, Finset.sum_eq_single ⟨i.val + 1, hi1⟩]
      · rw [if_pos ⟨rfl, hc.1, hc.2⟩]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨h1, -, -⟩
        exact hb (Fin.ext h1.symm)
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    · rw [dif_neg hi1]
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      rintro ⟨h1, -, -⟩
      have := b.2
      omega
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact hc ⟨by omega, h3⟩

theorem sl_sum_range_ite (n b : ℕ) (hb : b ≤ n) (f : ℕ → κ) :
    ∑ i ∈ Finset.range n, (if i < b then f i else 0) = ∑ i ∈ Finset.range b, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem sl_sup_ins {r k c j : ℕ} (hr : r = k + j + c) (Y Mx : ℕ → ℕ → κ)
    (hY1 : ∀ i, i + 1 < k → Y i (i + 1) = Mx i (i + 1)) (hY2 : ∀ i, k ≤ i → i < k + c → Y i (i + 1) = 0)
    (hY3 : ∀ i, k + c ≤ i → Y i (i + 1) = Mx (i - c) (i - c + 1)) :
    ∑ i ∈ Finset.range r, (if i + 1 < r ∧ i + 1 ≠ k then Y i (i + 1) else 0) =
      ∑ i ∈ Finset.range (k - 1), Mx i (i + 1) + ∑ i ∈ Finset.range (j - 1), Mx (k + i) (k + i + 1) := by
  have e : ∀ i ∈ Finset.range r, (if i + 1 < r ∧ i + 1 ≠ k then Y i (i + 1) else 0) =
      (if i < k - 1 then Mx i (i + 1) else 0) + (if k + c ≤ i ∧ i + 1 < r then Mx (i - c) (i - c + 1) else 0) := by
    intro i _
    by_cases h1 : i < k - 1
    · rw [if_pos (by omega), if_pos h1, if_neg (by omega), add_zero, hY1 i (by omega)]
    · by_cases h2 : k + c ≤ i ∧ i + 1 < r
      · rw [if_pos (by omega), if_neg h1, if_pos h2, zero_add, hY3 i h2.1]
      · rw [if_neg h1, if_neg h2, add_zero]
        by_cases h3 : i + 1 < r ∧ i + 1 ≠ k
        · rw [if_pos h3, hY2 i (by omega) (by omega)]
        · rw [if_neg h3]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, sl_sum_range_ite r (k - 1) (by omega)]
  congr 1
  rw [← Finset.sum_filter]
  have hf : (Finset.range r).filter (fun i => k + c ≤ i ∧ i + 1 < r) = Finset.Ico (k + c) (k + c + (j - 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Finset.sum_Ico_eq_sum_range, show k + c + (j - 1) - (k + c) = j - 1 by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show k + c + i - c = k + i by omega]

end LamEnt

section DetBlk

variable {κ K : Type} [CommRing κ] [Field K]

theorem sl_coarse_blk {r t j s a : ℕ} (ht : 0 < t) (hs : s < j) (ha : a < t) :
    coarse r (List.replicate j t) (r + s * t + a) = s + 1 := by
  have h1 : (s + 1) * t ≤ j * t := Nat.mul_le_mul_right t hs
  rw [Nat.add_mul, one_mul] at h1
  rw [coarse_rep ht (by omega), if_neg (by omega), add_assoc, Nat.add_sub_cancel_left,
    show s * t + a = a + s * t from add_comm _ _, Nat.add_mul_div_right a s ht, Nat.div_eq_of_lt ha, zero_add]

def blockPositionsEquiv {n r t j s : ℕ} (ht : 0 < t) (hn : n = r + j * t) (hs : s < j) :
    Fin t ≃ {i : Fin n // coarse r (List.replicate j t) i.val = s + 1} :=
  Equiv.ofBijective (fun a => ⟨⟨r + s * t + a.val, by
      have h1 : (s + 1) * t ≤ j * t := Nat.mul_le_mul_right t hs
      rw [Nat.add_mul, one_mul] at h1
      have := a.2
      omega⟩, sl_coarse_blk ht hs a.2⟩) (by
    constructor
    · intro a b hab
      have := congrArg (fun x : {i : Fin n // coarse r (List.replicate j t) i.val = s + 1} => x.1.val) hab
      simp only at this
      exact Fin.ext (by omega)
    · rintro ⟨i, hi⟩
      have hc := coarse_rep (r := r) (j := j) ht (show i.val ≤ r + j * t by have := i.2; omega)
      rw [hi] at hc
      by_cases hir : i.val < r
      · rw [if_pos hir] at hc
        omega
      · rw [if_neg hir] at hc
        have hd : (i.val - r) / t = s := by omega
        have h1 := Nat.div_mul_le_self (i.val - r) t
        have h2 := Nat.lt_div_mul_add (a := i.val - r) ht
        rw [hd] at h1 h2
        refine ⟨⟨i.val - r - s * t, by omega⟩, Subtype.ext (Fin.ext ?_)⟩
        show r + s * t + (i.val - r - s * t) = i.val
        omega)

theorem sl_blk_det {n r t j s : ℕ} (ht : 0 < t) (hn : n = r + j * t) (hs : s < j) (A : Matrix (Fin n) (Fin n) κ) :
    (A.toSquareBlock (fun i => coarse r (List.replicate j t) i.val) (s + 1)).det =
      (Matrix.of fun a b : Fin t => A (blockPositionsEquiv ht hn hs a).1 (blockPositionsEquiv ht hn hs b).1).det := by
  rw [← Matrix.det_submatrix_equiv_self (blockPositionsEquiv ht hn hs)]
  rfl

theorem sl_ocbChiK_unit (χ : κˣ →* Kˣ) (u : κˣ) : ocbChiK χ (u : κ) = ((χ u : Kˣ) : K) := by
  unfold ocbChiK
  rw [dif_pos u.isUnit]
  congr 2
  exact Units.ext rfl

end DetBlk

section InsEnt

variable {κ : Type} [CommRing κ] {N c k N' : ℕ} (hk : k ≤ N) (hN' : N' = N + c)

theorem sl_insEquiv_of_val (p : Fin N) (a : Fin N') (h : a.val = if p.val < k then p.val else p.val + c) :
    insEquiv N c k N' hk hN' a = Sum.inl p := by
  have : a = (insEquiv N c k N' hk hN').symm (Sum.inl p) := Fin.ext (by rw [sl_insEquiv_symm_val]; exact h)
  rw [this, Equiv.apply_symm_apply]

theorem sl_insEquiv_of_val_r (q : Fin c) (a : Fin N') (h : a.val = k + q.val) :
    insEquiv N c k N' hk hN' a = Sum.inr q := by
  have : a = (insEquiv N c k N' hk hN').symm (Sum.inr q) := Fin.ext h
  rw [this, Equiv.apply_symm_apply]

theorem sl_ocbM_ins (M : GL (Fin N) κ) (p p' : ℕ) (hp : p < N) (hp' : p' < N) :
    ocbM (insGL κ N c k N' hk hN' M) (if p < k then p else p + c) (if p' < k then p' else p' + c) = ocbM M p p' := by
  have b1 : (if p < k then p else p + c) < N' := by split_ifs <;> omega
  have b2 : (if p' < k then p' else p' + c) < N' := by split_ifs <;> omega
  unfold ocbM
  rw [dif_pos ⟨b1, b2⟩, dif_pos ⟨hp, hp'⟩, insGL_val, sl_insEquiv_of_val hk hN' ⟨p, hp⟩ _ rfl,
    sl_insEquiv_of_val hk hN' ⟨p', hp'⟩ _ rfl, Matrix.fromBlocks_apply₁₁]

theorem sl_ocbM_ins_row (M : GL (Fin N) κ) (i i' : ℕ) (hi1 : k ≤ i) (hi2 : i < k + c) (hne : i ≠ i') :
    ocbM (insGL κ N c k N' hk hN' M) i i' = 0 := by
  unfold ocbM
  split_ifs with hb
  · rw [insGL_val, sl_insEquiv_of_val_r hk hN' ⟨i - k, by omega⟩ ⟨i, hb.1⟩ (by dsimp only; omega)]
    by_cases h1 : i' < k
    · rw [sl_insEquiv_of_val hk hN' ⟨i', by omega⟩ ⟨i', hb.2⟩ (by dsimp only; rw [if_pos h1])]
      rfl
    · by_cases h2 : i' < k + c
      · rw [sl_insEquiv_of_val_r hk hN' ⟨i' - k, by omega⟩ ⟨i', hb.2⟩ (by dsimp only; omega), Matrix.fromBlocks_apply₂₂]
        exact Matrix.one_apply_ne fun e => hne (by have := congrArg Fin.val e; simp only at this; omega)
      · rw [sl_insEquiv_of_val hk hN' ⟨i' - c, by omega⟩ ⟨i', hb.2⟩ (by dsimp only; split_ifs <;> omega)]
        rfl
  · rfl

theorem sl_ocbM_ins_late (M : GL (Fin N) κ) (i i' : ℕ) (hi : k + c ≤ i) (hi' : k + c ≤ i') :
    ocbM (insGL κ N c k N' hk hN' M) i i' = ocbM M (i - c) (i' - c) := by
  unfold ocbM
  by_cases hb : i < N' ∧ i' < N'
  · rw [dif_pos hb, dif_pos ⟨by omega, by omega⟩, insGL_val,
      sl_insEquiv_of_val hk hN' ⟨i - c, by omega⟩ ⟨i, hb.1⟩ (by dsimp only; split_ifs <;> omega),
      sl_insEquiv_of_val hk hN' ⟨i' - c, by omega⟩ ⟨i', hb.2⟩ (by dsimp only; split_ifs <;> omega), Matrix.fromBlocks_apply₁₁]
  · rw [dif_neg hb, dif_neg (by omega)]

end InsEnt

section LamAsm

variable {κ K : Type} [CommRing κ] [Field K]

theorem character_level_zero_entries (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n k m t : ℕ} (hn : n = k) (M : ↥(HX κ n k t 0)) :
    ((lamX ψ χ n k m t 0 M : Kˣ) : K) = ocbXLam ψ χ k 0 t M.1 := by
  subst hn
  unfold lamX lamGen ocbXLam
  rw [MonoidHom.mul_apply, Units.val_mul, supChar_val, MonoidHom.comp_apply, detChar_apply, List.length_replicate]
  simp only [Finset.range_zero, Finset.prod_empty, Units.val_one, mul_one, Nat.zero_sub, Finset.sum_empty, add_zero]
  congr 1
  rw [sl_supSum_eq, ← sl_sum_range_ite n (n - 1) (by omega)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold SX
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases hc : i < n - 1
  · rw [if_pos ⟨by omega, by omega, Or.inl (by omega)⟩, if_pos hc, dif_pos (by omega)]
    unfold ocbM
    rw [dif_pos ⟨by omega, by omega⟩]
  · rw [if_neg (by omega), if_neg hc]

theorem sl_lamJsym_ent (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n k r t j rS c N : ℕ} (h : r ≤ n) (hr0 : r = k + 2 * rS + 1)
    (hr : r = k + j + c) (hn : n = r + j * t) (ht : 0 < t) (M : ↥(HJsym κ n k r t j rS h)) (Mx : GL (Fin N) κ)
    (hY1 : ∀ i, i + 1 < k → ocbM M.1 i (i + 1) = ocbM Mx i (i + 1))
    (hY2 : ∀ i, k ≤ i → i < k + c → ocbM M.1 i (i + 1) = 0)
    (hY3 : ∀ i, k + c ≤ i → ocbM M.1 i (i + 1) = ocbM Mx (i - c) (i - c + 1))
    (hB : ∀ s, s < j → ∀ a b : ℕ, ocbM M.1 (r + s * t + a) (r + s * t + b) = ocbM Mx (k + j + s * t + a) (k + j + s * t + b)) :
    ((lamJsym ψ χ n k r t j rS h M : Kˣ) : K) = ocbXLam ψ χ k j t Mx := by
  unfold lamJsym lamPar ocbXLam
  rw [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, MonoidHom.comp_apply, chiSymF_val hr0, detChar_apply,
    Units.coe_prod, List.length_replicate]
  congr 1
  · congr 1
    rw [sl_supSum_eq, ← sl_sup_ins hr (ocbM M.1) (ocbM Mx) hY1 hY2 hY3]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold SPsymF
    simp only [Finset.mem_filter, Finset.mem_range]
    by_cases hc : i + 1 < r ∧ i + 1 ≠ k
    · rw [if_pos ⟨hc.1, by omega, hc.2⟩, if_pos hc, dif_pos hc.1]
      unfold ocbM
      rw [dif_pos ⟨by omega, by omega⟩]
      rfl
    · rw [if_neg (fun hh => hc ⟨hh.1, hh.2.2⟩), if_neg hc]
  · refine Finset.prod_congr rfl fun s hs => ?_
    have hs' : s < j := Finset.mem_range.mp hs
    rw [← sl_ocbChiK_unit, blkDet_val, sl_blk_det ht hn hs']
    congr 2
    ext a b
    rw [Matrix.of_apply, Matrix.of_apply, ← hB s hs' a.1 b.1]
    unfold ocbM
    rw [dif_pos ⟨(blockPositionsEquiv ht hn hs' a).1.2, (blockPositionsEquiv ht hn hs' b).1.2⟩]
    rfl

end LamAsm

theorem closedLevels_by_entries_holds : OcbLevIsSym := by
  intro X Pr R Ch m2 hm
  refine ⟨sl_ocbH Ch m2 hm, fun j hj w hbar => ?_⟩
  have hr := r_eq_sym R
  have hrm : R.r = R.k + R.m - 1 := rfl
  have hN := N_eq_blocks R j
  have hpsi : psi0P Ch w.1 = Ch.psi0 w := by
    unfold psi0P
    rw [dif_pos w.2]
  have hchi : chiP Ch w.1 = extChi (fun s => Ch.chi s w) := by
    unfold chiP
    rw [dif_pos w.2]
    rfl
  rw [hpsi, hchi]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N 0),
        l = ⟨HX _ (R.N 0) R.k R.t 0, lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N 0) R.k R.m R.t 0⟩ →
        ∀ M : ↥l.H, ((l.lam M : X.Kˣ) : X.K) = ocbXLam (Ch.psi0 w) (extChi fun s => Ch.chi s w) R.k 0 R.t M.1 := by
      intro l hl M
      subst hl
      exact character_level_zero_entries _ _ (by simp [Ranks.N]) M
    exact key _ (by unfold colLevSym; rw [if_pos rfl]; unfold colLev; rw [if_pos (by omega)]) hbar
  · by_cases htop : j + 1 = R.m
    · have hNp := N_pred_eq htop
      have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j),
          l = ⟨HJsym _ (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le htop.ge),
            lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le htop.ge)⟩ →
          ∀ M : ↥l.H, ((l.lam M : X.Kˣ) : X.K) = ocbXLam (Ch.psi0 w) (extChi fun s => Ch.chi s w) R.k j R.t M.1 := by
        intro l hl M
        subst hl
        refine sl_lamJsym_ent _ _ _ hr (c := 0) (by omega) hNp (t_pos R) M M.1 (fun i _ => rfl) (fun i h1 h2 => by omega)
          (fun i _ => by simp) (fun s _ a b => ?_)
        rw [show R.r + s * R.t + a = R.k + j + s * R.t + a by omega, show R.r + s * R.t + b = R.k + j + s * R.t + b by omega]
      exact key _ (by rw [colLevSym_pred Ch htop]; rfl) hbar
    · have h1 : j + 1 < R.m := by omega
      have hM : insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl hbar.1 ∈
          HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega)) := by
        have key : ∀ x, x ∈ (colLevSym Ch j w).H → insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j))
            (colK_le_N R j) rfl x ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega)) := by
          intro x hx
          rw [colLevSym_mid_H Ch (by omega) h1 w] at hx
          exact hx
        exact key hbar.1 hbar.2
      rw [colLevSym_mid_lam Ch (by omega) h1 w hbar hM]
      have hk := colK_le_N R j
      refine sl_lamJsym_ent _ _ _ hr (c := R.m - 1 - j) (by omega) (by omega) (t_pos R) ⟨_, hM⟩ hbar.1
        (fun i hi => ?_) (fun i i1 i2 => sl_ocbM_ins_row (c := R.m - 1 - j) hk rfl hbar.1 i (i + 1) i1 i2 (by omega))
        (fun i hi => ?_) (fun s hs a b => ?_)
      · have := sl_ocbM_ins (c := R.m - 1 - j) hk rfl hbar.1 i (i + 1) (by omega) (by omega)
        rwa [if_pos (by omega), if_pos (by omega)] at this
      · show ocbM (insGL _ _ _ _ _ hk rfl hbar.1) i (i + 1) = _
        rw [sl_ocbM_ins_late (c := R.m - 1 - j) hk rfl hbar.1 i (i + 1) hi (by omega), show i + 1 - (R.m - 1 - j) = i - (R.m - 1 - j) + 1 by omega]
      · show ocbM (insGL _ _ _ _ _ hk rfl hbar.1) _ _ = _
        rw [sl_ocbM_ins_late (c := R.m - 1 - j) hk rfl hbar.1 _ _ (by omega) (by omega),
          show R.r + s * R.t + a - (R.m - 1 - j) = R.k + j + s * R.t + a by omega,
          show R.r + s * R.t + b - (R.m - 1 - j) = R.k + j + s * R.t + b by omega]

end Formalism.L2.Col
