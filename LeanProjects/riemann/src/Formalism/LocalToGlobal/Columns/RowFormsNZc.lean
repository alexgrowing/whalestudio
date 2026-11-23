import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.RowFormsNZp

open MvPolynomial NumberField
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.GradedWeylDivisibility

section One

variable (K : Type) [Field K] {n : ℕ}

theorem nz_rowAct_X (s : Equiv.Perm (Fin n)) (v : Fin n × Fin n) :
    rowAct K (n := n) (pM K s)ᵀ (X v) = X (s v.1, v.2) := by
  unfold rowAct
  rw [aeval_X, Finset.sum_eq_single (s v.1)]
  · rw [Matrix.transpose_apply, pM_apply, if_pos rfl, C_1, one_mul]
  · intro b _ hb
    rw [Matrix.transpose_apply, pM_apply, if_neg hb, C_0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem nz_rowAct_minor (s : Equiv.Perm (Fin n)) (i : ℕ) (hi : i ≤ n) :
    rowAct K (n := n) (pM K s)ᵀ (lpMinor K i hi hi) =
      (Matrix.of fun p q : Fin i => (X (s (Fin.castLE hi p), Fin.castLE hi q) : MvPolynomial (Fin n × Fin n) K)).det := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  refine Matrix.ext fun p q => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact nz_rowAct_X K s _

theorem nz_minor_swap_in {a b : Fin n} (hab : a < b) (i : ℕ) (hi : i ≤ n) (hb : b.val < i) :
    rowAct K (n := n) (pM K (Equiv.swap a b))ᵀ (lpMinor K i hi hi) = -lpMinor K i hi hi := by
  rw [nz_rowAct_minor]
  have ha : a.val < i := lt_trans hab hb
  have hne : (⟨a.val, ha⟩ : Fin i) ≠ ⟨b.val, hb⟩ := fun h => (ne_of_lt hab) (Fin.ext (Fin.mk.inj_iff.mp h))
  have h1 : (Matrix.of fun p q : Fin i => (X (Equiv.swap a b (Fin.castLE hi p), Fin.castLE hi q) : MvPolynomial (Fin n × Fin n) K)) =
      (Matrix.of fun p q : Fin i => (X (Fin.castLE hi p, Fin.castLE hi q) : MvPolynomial (Fin n × Fin n) K)).submatrix
        (Equiv.swap (⟨a.val, ha⟩ : Fin i) ⟨b.val, hb⟩) id := by
    refine Matrix.ext fun p q => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
    have key : Equiv.swap a b (Fin.castLE hi p) = Fin.castLE hi (Equiv.swap (⟨a.val, ha⟩ : Fin i) ⟨b.val, hb⟩ p) := by
      by_cases hpa : p = ⟨a.val, ha⟩
      · subst hpa
        rw [Equiv.swap_apply_left]
        have : Fin.castLE hi ⟨a.val, ha⟩ = a := Fin.ext rfl
        rw [this, Equiv.swap_apply_left]
        exact Fin.ext rfl
      · by_cases hpb : p = ⟨b.val, hb⟩
        · subst hpb
          rw [Equiv.swap_apply_right]
          have : Fin.castLE hi ⟨b.val, hb⟩ = b := Fin.ext rfl
          rw [this, Equiv.swap_apply_right]
          exact Fin.ext rfl
        · rw [Equiv.swap_apply_of_ne_of_ne hpa hpb, Equiv.swap_apply_of_ne_of_ne]
          · intro h
            exact hpa (Fin.ext (show p.val = a.val from congrArg Fin.val h))
          · intro h
            exact hpb (Fin.ext (show p.val = b.val from congrArg Fin.val h))
    rw [key]
  rw [h1, Matrix.det_permute, Equiv.Perm.sign_swap hne]
  unfold lpMinor
  simp

theorem nz_minor_swap_out {a b : Fin n} (hab : a < b) (i : ℕ) (hi : i ≤ n) (ha : i ≤ a.val) :
    rowAct K (n := n) (pM K (Equiv.swap a b))ᵀ (lpMinor K i hi hi) = lpMinor K i hi hi := by
  rw [nz_rowAct_minor]
  unfold lpMinor
  congr 1
  refine Matrix.ext fun p q => ?_
  simp only [Matrix.of_apply]
  rw [Equiv.swap_apply_of_ne_of_ne]
  · intro h
    have h1 : p.val = a.val := congrArg Fin.val h
    have := p.2
    omega
  · intro h
    have h1 : p.val = b.val := congrArg Fin.val h
    have := p.2
    have h2 : a.val < b.val := hab
    omega

theorem nz_tel (ν : Fin n → ℕ) (hν : Antitone ν) (b : Fin n) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => b ≤ i), (ν i - nuNext ν i) = ν b := by
  obtain ⟨k, hk⟩ : ∃ k, k = n - b.val := ⟨_, rfl⟩
  induction k generalizing b with
  | zero => have := b.2; omega
  | succ k ih =>
    by_cases hb : b.val + 1 < n
    · have hfil : Finset.univ.filter (fun i : Fin n => b ≤ i) =
          insert b (Finset.univ.filter (fun i : Fin n => (⟨b.val + 1, hb⟩ : Fin n) ≤ i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
        omega
      have hnot : b ∉ Finset.univ.filter (fun i : Fin n => (⟨b.val + 1, hb⟩ : Fin n) ≤ i) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
        omega
      rw [hfil, Finset.sum_insert hnot, ih ⟨b.val + 1, hb⟩ (by simp only; omega)]
      have h1 : nuNext ν b = ν ⟨b.val + 1, hb⟩ := by
        unfold nuNext
        rw [dif_pos hb]
      have h2 : ν ⟨b.val + 1, hb⟩ ≤ ν b := hν (by rw [Fin.le_def]; simp)
      rw [h1]
      omega
    · have hfil : Finset.univ.filter (fun i : Fin n => b ≤ i) = {b} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
        have := i.2
        omega
      have h1 : nuNext ν b = 0 := by
        unfold nuNext
        rw [dif_neg hb]
      rw [hfil, Finset.sum_singleton, h1, Nat.sub_zero]

theorem nz_hw_swap (ν : Fin n → ℕ) (hν : Antitone ν) {a b : Fin n} (hab : a < b) (h : ν a = ν b) :
    rowAct K (n := n) (pM K (Equiv.swap a b))ᵀ (hw K le_rfl ν) = (-1) ^ ν b * hw K le_rfl ν := by
  unfold hw
  rw [map_prod]
  have h1 : ∀ i : Fin n, rowAct K (n := n) (pM K (Equiv.swap a b))ᵀ
      ((lpMinor K (i.val + 1) (by omega) (by omega)) ^ (ν i - nuNext ν i)) =
      (if b ≤ i then (-1 : MvPolynomial (Fin n × Fin n) K) ^ (ν i - nuNext ν i) else 1) *
        (lpMinor K (i.val + 1) (by omega) (by omega)) ^ (ν i - nuNext ν i) := by
    intro i
    rw [map_pow]
    by_cases hbi : b ≤ i
    · rw [if_pos hbi, nz_minor_swap_in K hab _ _ (by rw [Fin.le_def] at hbi; omega), neg_pow]
    · rw [if_neg hbi, one_mul]
      by_cases hai : i < a
      · rw [nz_minor_swap_out K hab _ _ (by rw [Fin.lt_def] at hai; omega)]
      · have hib : i.val + 1 < n := by
          rw [Fin.le_def] at hbi
          have := b.2
          omega
        have e1 : nuNext ν i = ν ⟨i.val + 1, hib⟩ := by
          unfold nuNext
          rw [dif_pos hib]
        have e2 : ν i ≤ ν a := hν (not_lt.mp hai)
        have e3 : ν b ≤ ν ⟨i.val + 1, hib⟩ := hν (by rw [Fin.le_def] at hbi ⊢; simp only; omega)
        have e4 : ν i - nuNext ν i = 0 := by rw [e1]; omega
        rw [e4, pow_zero, pow_zero]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, nz_tel ν hν b]

theorem nz_det_pM (s : Equiv.Perm (Fin n)) : (pM K s).det = ((Equiv.Perm.sign s : ℤˣ) : ℤ) := by
  have h : pM K s = (1 : Matrix (Fin n) (Fin n) K).submatrix (s⁻¹ : Equiv.Perm (Fin n)) id := by
    ext i j
    rw [pM_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    by_cases hij : i = s j
    · rw [if_pos hij, if_pos (by rw [hij]; simp)]
    · rw [if_neg hij, if_neg (fun h' => hij (by rw [← h']; simp))]
  rw [h, Matrix.det_permute, Matrix.det_one, mul_one, Equiv.Perm.sign_inv]

theorem nz_sqAct_swap (lam : DomWeight n) {a b : Fin n} (hab : a < b) (h : lam.w a = lam.w b) :
    sqAct K n lam (permGL K (Equiv.swap a b)) (extremal K n lam) = ((-1 : K) ^ lam.w b) • extremal K n lam := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) b.2
  have hge : ∀ x : Fin n, lam.detShift ≤ lam.w x := by
    intro x
    unfold DomWeight.detShift
    rw [dif_pos hn]
    exact lam.anti (by rw [Fin.le_def]; have := x.2; simp only; omega)
  have hnat : ∀ x : Fin n, ((lam.natW x : ℕ) : ℤ) = lam.w x - lam.detShift := by
    intro x
    unfold DomWeight.natW
    rw [Int.toNat_of_nonneg (by have := hge x; omega)]
  have hab' : lam.natW a = lam.natW b := by
    have := hnat a
    have := hnat b
    omega
  unfold sqAct extremal
  rw [permGL_val, nz_hw_swap K lam.natW (natW_antitone lam) hab hab']
  have hdet : detPow K n (permGL K (Equiv.swap a b)) lam.detShift = (-1 : K) ^ lam.detShift := by
    unfold detPow
    rw [Units.val_zpow_eq_zpow_val]
    congr 1
    show ((permGL K (Equiv.swap a b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = -1
    rw [permGL_val, nz_det_pM, Equiv.Perm.sign_swap (ne_of_lt hab)]
    simp
  rw [hdet]
  have hw : lam.w b = lam.detShift + ((lam.natW b : ℕ) : ℤ) := by rw [hnat b]; ring
  rw [hw, zpow_add₀ (by norm_num : (-1 : K) ≠ 0), zpow_natCast, mul_smul]
  congr 1
  rw [smul_eq_C_mul, map_pow, map_neg, C_1]

end One

section All

variable (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def nzExt (lam : ι → DomWeight n) : VV K lam := ⟨extVV K lam, extVV_mem K lam⟩

theorem nzExt_ne_zero (lam : ι → DomWeight n) : nzExt K lam ≠ 0 :=
  fun h => extVV_ne_zero K lam (congrArg Subtype.val h)

theorem nz_prod_zpow (u : K) (hu : u ≠ 0) (f : ι → ℤ) (S : Finset ι) : ∏ τ ∈ S, u ^ f τ = u ^ ∑ τ ∈ S, f τ := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hu]

theorem nz_ten_smul (c : ι → K) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    ten (fun τ => c τ • f τ) = (∏ τ, c τ) • ten f := by
  unfold ten
  simp only [map_smul]
  rw [Finset.prod_smul]

theorem nz_rhoK_swap_lt (lam : ι → DomWeight n) {a b : Fin n} (hab : a < b) (h : ∀ τ, (lam τ).w a = (lam τ).w b) :
    rhoK lam (fun _ => permGL K (Equiv.swap a b)) (nzExt K lam) = ((-1 : K) ^ ∑ τ, (lam τ).w b) • nzExt K lam := by
  apply Subtype.ext
  rw [rhoK_coe]
  show actP lam (fun _ => permGL K (Equiv.swap a b)) (ten fun τ => extremal K n (lam τ)) =
    ((-1 : K) ^ ∑ τ, (lam τ).w b) • ten fun τ => extremal K n (lam τ)
  rw [actTen K ι n lam]
  have h1 : (fun τ => sqAct K n (lam τ) (permGL K (Equiv.swap a b)) (extremal K n (lam τ))) =
      fun τ => ((-1 : K) ^ (lam τ).w b) • extremal K n (lam τ) :=
    funext fun τ => nz_sqAct_swap K (lam τ) hab (h τ)
  rw [h1, nz_ten_smul, nz_prod_zpow K (-1) (by norm_num)]

theorem nz_rhoK_swap (lam : ι → DomWeight n) {a b : Fin n} (hab : a ≠ b) (h : ∀ τ, (lam τ).w a = (lam τ).w b)
    (he : Even (∑ τ, (lam τ).w a)) :
    rhoK lam (fun _ => permGL K (Equiv.swap a b)) (nzExt K lam) = nzExt K lam := by
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have he' : Even (∑ τ, (lam τ).w b) := by
      rw [← Finset.sum_congr rfl fun τ _ => h τ]
      exact he
    rw [nz_rhoK_swap_lt K lam hlt h, he'.neg_one_zpow, one_smul]
  · rw [Equiv.swap_comm, nz_rhoK_swap_lt K lam hlt (fun τ => (h τ).symm), he.neg_one_zpow, one_smul]

theorem nz_rhoK_perm (lam : ι → DomWeight n) (s : Equiv.Perm (Fin n)) (h1 : ∀ τ x, (lam τ).w (s x) = (lam τ).w x)
    (h2 : ∀ x, s x ≠ x → Even (∑ τ, (lam τ).w x)) :
    rhoK lam (fun _ => permGL K s) (nzExt K lam) = nzExt K lam := by
  obtain ⟨k, hk⟩ : ∃ k, s.support.card = k := ⟨_, rfl⟩
  induction k using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    by_cases hs : s = 1
    · subst hs
      have : (fun _ : ι => permGL K (1 : Equiv.Perm (Fin n))) = 1 := by
        funext τ
        rw [map_one]
        rfl
      rw [this, map_one]
      rfl
    · obtain ⟨x, hx⟩ : ∃ x, s x ≠ x := by
        by_contra hc
        push Not at hc
        exact hs (Equiv.ext hc)
      set s' : Equiv.Perm (Fin n) := Equiv.swap x (s x) * s with hs'
      have hcard : s'.support.card < k := by
        rw [← hk]
        exact Equiv.Perm.card_support_swap_mul hx
      have hsw : ∀ τ y, (lam τ).w (Equiv.swap x (s x) y) = (lam τ).w y := by
        intro τ y
        by_cases hy1 : y = x
        · rw [hy1, Equiv.swap_apply_left, h1]
        · by_cases hy2 : y = s x
          · rw [hy2, Equiv.swap_apply_right, h1]
          · rw [Equiv.swap_apply_of_ne_of_ne hy1 hy2]
      have h1' : ∀ τ y, (lam τ).w (s' y) = (lam τ).w y := by
        intro τ y
        rw [hs', Equiv.Perm.mul_apply, hsw, h1]
      have h2' : ∀ y, s' y ≠ y → Even (∑ τ, (lam τ).w y) := by
        intro y hy
        apply h2
        intro hsy
        apply hy
        rw [hs', Equiv.Perm.mul_apply, hsy]
        apply Equiv.swap_apply_of_ne_of_ne
        · intro hyx
          exact hx (by rw [← hyx]; exact hsy)
        · intro hyx
          have : s y = s x := by rw [hsy]; exact hyx
          exact hx (by rw [← s.injective this]; exact hsy)
      have hdec : s = Equiv.swap x (s x) * s' := by
        rw [hs', ← mul_assoc, Equiv.swap_mul_self, one_mul]
      have hfun : (fun _ : ι => permGL K s) =
          (fun _ : ι => permGL K (Equiv.swap x (s x))) * fun _ : ι => permGL K s' := by
        funext τ
        rw [Pi.mul_apply, ← map_mul, ← hdec]
      rw [hfun, map_mul, Module.End.mul_apply, ih _ hcard s' h1' h2' rfl]
      exact nz_rhoK_swap K lam (Ne.symm hx) (fun τ => (h1 τ x).symm) (h2 x hx)

end All

section Emb

variable {E : Type} [Field E] (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K)

theorem nz_embGL_perm (s : Equiv.Perm (Fin n)) : embGL emb (permGL E s) = fun _ => permGL K s := by
  funext τ
  apply Units.ext
  rw [embGL_coe, permGL_val, permGL_val, pM_map]

theorem nz_invTrK_perm (s : Equiv.Perm (Fin n)) :
    invTrK (fun _ : ι => permGL K s) = fun _ => permGL K s := by
  funext τ
  apply Units.ext
  rw [invTrK_coe, ← map_inv, permGL_val, permGL_val, pM_transpose, inv_inv]

theorem nz_rhoV_perm (lam : ι → DomWeight n) (s : Equiv.Perm (Fin n)) (h1 : ∀ τ x, (lam τ).w (s x) = (lam τ).w x)
    (h2 : ∀ x, s x ≠ x → Even (∑ τ, (lam τ).w x)) :
    rhoV emb lam (permGL E s) (nzExt K lam) = nzExt K lam := by
  show rhoK lam (embGL emb (permGL E s)) (nzExt K lam) = nzExt K lam
  rw [nz_embGL_perm]
  exact nz_rhoK_perm K lam s h1 h2

theorem nz_rhoVr_perm (lam : ι → DomWeight n) (s : Equiv.Perm (Fin n)) (h1 : ∀ τ x, (lam τ).w (s x) = (lam τ).w x)
    (h2 : ∀ x, s x ≠ x → Even (∑ τ, (lam τ).w x)) :
    rhoVr emb lam (permGL E s) (nzExt K lam) = nzExt K lam := by
  show rhoK lam (invTrK (embGL emb (permGL E s))) (nzExt K lam) = nzExt K lam
  rw [nz_embGL_perm, nz_invTrK_perm]
  exact nz_rhoK_perm K lam s h1 h2

end Emb

end Formalism.L2.Col
