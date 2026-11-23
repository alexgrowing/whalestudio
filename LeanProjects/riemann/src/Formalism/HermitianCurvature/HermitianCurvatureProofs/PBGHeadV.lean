import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHead
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem headAlg_gen (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r m : ℕ)
    (hm : m + 2 ≤ r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c c' u : ℂ)
    (hG : Formalism.REAL.GlRel E)
    (hR : ∀ (x : A) (p q : Fin (2 * r + k + 1)), p.val < q.val → q.val < r →
      La (x * E p q) = (if q.val = p.val + 1 then (1 : ℂ) else 0) • La x)
    (hZ : Z.det ≠ 0) (hc : c ≠ 0)
    (hL : ∀ (b : Fin (m + 1)) (x : A), La (E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨b, by omega⟩) * x) =
      (c' * Z⁻¹ b (Fin.last m)) • La x)
    (hxi : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), xi ⟨a, by omega⟩ q = if h : q.val < m + 1 then Z a ⟨q, h⟩ else 0)
    (hxl : ∀ q : Fin (2 * r + k + 1), xi ⟨m + 1, by omega⟩ q = if q.val = m + 1 then c else 0) :
    (Z.det * c)⁻¹ • La (C3.AAx k r E xi (m + 2) hm u) =
      Z.det⁻¹ • La (C3.AAx k r E xi (m + 1) (by omega) u *
          (algebraMap ℂ A (u - ((m + 1 : ℕ) : ℂ)) + E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩))) -
        (c' * Z.det⁻¹) • La (C3.AAx k r E xi m (by omega) u) := by
  have hxi' : ∀ (a : Fin r) (q : Fin (2 * r + k + 1)) (ha : a.val < m + 1),
      xi a q = if h : q.val < m + 1 then Z ⟨a.val, ha⟩ ⟨q.val, h⟩ else 0 := by
    intro a q ha; have := hxi ⟨a.val, ha⟩ q; simpa using this
  have hxl' : ∀ (a : Fin r) (q : Fin (2 * r + k + 1)), a.val = m + 1 → xi a q = if q.val = m + 1 then c else 0 := by
    intro a q ha
    have e : a = ⟨m + 1, by omega⟩ := Fin.ext ha
    rw [e]; exact hxl q

  have hA2 : AAx k r E xi (m + 2) hm u = (Z.det * c) • qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u := by
    rw [AAx_head k r E xi (m + 2) hm (Matrix.of fun a b : Fin (m + 2) => xi (Fin.castLE hm a) (xR k r (m + 2) hm b)) u
      ?_ (fun a b => rfl)]
    · congr 1
      rw [Matrix.det_succ_row _ (Fin.last (m + 1)), Fin.sum_univ_castSucc, Finset.sum_eq_zero]
      · simp only [Matrix.of_apply, Matrix.submatrix, Fin.succAbove_last, zero_add]
        have h1 : xi (Fin.castLE hm (Fin.last (m + 1))) (xR k r (m + 2) hm (Fin.last (m + 1))) = c := by
          rw [hxl' _ _ (by simp), if_pos (by simp [xR, eI])]
        rw [h1]
        have h2 : (Matrix.of fun i j : Fin (m + 1) => xi (Fin.castLE hm (Fin.castSucc i))
            (xR k r (m + 2) hm (Fin.castSucc j))) = Z := by
          ext i j
          simp only [Matrix.of_apply]
          rw [hxi' _ _ (by simp <;> omega), dif_pos (by simp [xR, eI] <;> omega)]
          congr 1
        rw [h2]
        simp only [Fin.val_last]
        rw [← two_mul, pow_mul]; norm_num; ring
      · intro j _
        simp only [Matrix.of_apply]
        rw [hxl' _ _ (by simp), if_neg (by simp [xR, eI]; omega)]
        ring
    · intro a p ha hp
      by_cases ha' : a.val < m + 1
      · rw [hxi' a p ha', dif_neg (by omega)]
      · rw [hxl' a p (by omega), if_neg (by omega)]
  have hA1 : AAx k r E xi (m + 1) (by omega) u = Z.det • qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u := by
    rw [AAx_head k r E xi (m + 1) (by omega) Z u]
    · intro a p ha hp
      rw [hxi' a p ha, dif_neg (by omega)]
    · intro a b
      rw [hxi' _ _ (by simp <;> omega), dif_pos (by simp [xR, eI] <;> omega)]
      congr 1
  have hA0 : AAx k r E xi m (by omega) u = ∑ l0 : Fin (m + 1),
      (Z.submatrix Fin.castSucc l0.succAbove).det •
        qminor E (xR k r m (by omega)) (xR k r (m + 1) (by omega) ∘ l0.succAbove) u := by
    rw [AAx_omit k r m (by omega) E xi u]
    · apply Finset.sum_congr rfl
      intro l0 _
      congr 2
      ext a l
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      rw [hxi' _ _ (by simp <;> omega), dif_pos (by simp [xR, eI] <;> omega)]
      congr 1
    · intro a p ha hp
      rw [hxi' a p (by omega), dif_neg (by omega)]

  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hmain : La (qminor E a a u) = La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
    rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
      intro l
      rw [la_intmul]
      have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
        intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
      rw [tm_offdiag _ _ hne, hR _ _ _ (by rw [hav, hav]; simp <;> omega) (by rw [hav]; simp <;> omega),
        if_neg (by rw [hav, hav]; simp <;> omega), zero_smul, smul_zero]
    rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]
    have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
        La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) := by
      rw [la_intmul, Fin.succAbove_last, hcs]
      have h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
      rw [h1]
      have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
        simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
      rw [h2]; simp
    rw [hlast]
    have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
        La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
      have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
        intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
      rw [tm_offdiag _ _ hne, hR _ _ _ (by rw [hav, hav]; simp) (by rw [hav]; simp <;> omega),
        if_pos (by rw [hav, hav]; simp), one_smul]
    rw [la_intmul, hmT]
    have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
      simp only [Fin.val_castSucc, Fin.val_last]
      push_cast
      rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
    rw [h3, neg_one_smul]; abel

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [eI]
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [xR, eI]; omega
  have hQ : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      ∑ l : Fin (m + 1), ((-1 : ℂ) ^ (m + (l : ℕ)) * (c' * Z⁻¹ l (Fin.last m))) •
        La (qminor E (xR k r m (by omega)) (xR k r (m + 1) (by omega) ∘ l.succAbove) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [la_intmul]
    have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
    have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
    rw [hr0, hrs, hcs]
    have hx : xR k r (m + 1) (by omega) l = eI k r ⟨l.val, by omega⟩ := by ext; simp [xR, eI]
    have hne : eI k r ⟨m + 1, by omega⟩ ≠ eI k r ⟨l.val, by omega⟩ := by
      intro h'; have := congrArg Fin.val h'; simp [eI] at this; omega
    rw [hx, tm_offdiag _ _ hne, hL l, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [pow_add]
    try ring
  have hT : Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) =
      algebraMap ℂ A (u - ((m + 1 : ℕ) : ℂ)) + E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) := by
    simp [Tm]
  rw [hA2, hA1, hA0, map_smul, smul_smul, inv_mul_cancel₀ (mul_ne_zero hZ hc), one_smul, smul_mul_assoc, map_smul,
    smul_smul, inv_mul_cancel₀ hZ, one_smul, map_sum, hmain, hQ, hT, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul, smul_smul, inv_last Z hZ]
  congr 1
  have hs : ((-1 : ℂ) ^ (m + (l : ℕ))) * (-1) ^ (m + (l : ℕ)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (c' * Z.det⁻¹ * (Z.submatrix Fin.castSucc l.succAbove).det) * hs

section mirror

variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}

def rv (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := Fin.rev p

def ep (p : Fin (2 * r + k + 1)) : ℂ := (-1 : ℂ) ^ (p : ℕ)

theorem ep_sq (p : Fin (2 * r + k + 1)) : ep p * ep p = 1 := by
  unfold ep
  rw [← mul_pow]
  norm_num

theorem rv_rv (p : Fin (2 * r + k + 1)) : rv (rv p) = p := Fin.rev_rev p

theorem rv_val (p : Fin (2 * r + k + 1)) : (rv p).val = 2 * r + k - p.val := by
  simp only [rv, Fin.val_rev]
  omega

theorem rv_eI (b : Fin r) : rv (eI k r b) = esI k r b := by
  apply Fin.ext
  rw [rv_val]
  simp [eI, esI]

def Emir (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (p q : Fin (2 * r + k + 1)) : A :=
  -((ep p * ep q) • E (rv q) (rv p))

theorem Emir_gl {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} (hE : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (Emir E) := by
  intro a b c d
  have hinj : ∀ x y : Fin (2 * r + k + 1), rv x = rv y ↔ x = y := fun x y =>
    ⟨fun h => by rw [← rv_rv x, h, rv_rv], fun h => h ▸ rfl⟩
  have key := hE (rv b) (rv a) (rv d) (rv c)
  simp only [hinj] at key
  have h1 : Emir E a b * Emir E c d - Emir E c d * Emir E a b =
      (ep a * ep b * (ep c * ep d)) •
        (E (rv b) (rv a) * E (rv d) (rv c) - E (rv d) (rv c) * E (rv b) (rv a)) := by
    simp only [Emir, neg_mul_neg, smul_mul_smul_comm, smul_sub, mul_comm (ep c * ep d) (ep a * ep b)]
  rw [h1, key]
  by_cases hbc : b = c
  · subst c
    by_cases hda : d = a
    · subst a
      have hs : ep d * ep b * (ep b * ep d) = 1 := by
        calc _ = (ep d * ep d) * (ep b * ep b) := by ring
          _ = 1 := by rw [ep_sq, ep_sq, mul_one]
      simp only [if_true, hs, one_smul, Emir, ep_sq, neg_sub_neg]
    · have hs : ep a * ep b * (ep b * ep d) = ep a * ep d := by
        calc _ = ep a * ep d * (ep b * ep b) := by ring
          _ = _ := by rw [ep_sq, mul_one]
      have had : ¬ a = d := fun e => hda e.symm
      simp only [if_true, had, hda, if_false, hs, Emir, zero_sub, sub_zero, smul_neg]
  · by_cases hda : d = a
    · subst a
      have hs : ep d * ep b * (ep c * ep d) = ep c * ep b := by
        calc _ = ep c * ep b * (ep d * ep d) := by ring
          _ = _ := by rw [ep_sq, mul_one]
      have hcb : ¬ c = b := fun e => hbc e.symm
      simp only [if_true, hcb, hbc, if_false, hs, Emir, zero_sub, sub_zero, neg_neg]
    · have had : ¬ a = d := fun e => hda e.symm
      have hcb : ¬ c = b := fun e => hbc e.symm
      simp only [had, hcb, hbc, hda, if_false, sub_zero, smul_zero]

theorem Tm_Emir (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (v : ℂ) (p q : Fin (2 * r + k + 1)) :
    Tm (Emir E) v p q = (ep p * ep q) • Tm (Formalism.FourierDecayAlt.P.Qx5.Eop E) v (rv p) (rv q) := by
  by_cases h : p = q
  · subst q
    simp only [Tm, Emir, Formalism.FourierDecayAlt.P.Qx5.Eop, if_true, ep_sq, one_smul]
  · have h' : ¬ rv p = rv q := fun e => h (by rw [← rv_rv p, e, rv_rv])
    simp only [Tm, Emir, Formalism.FourierDecayAlt.P.Qx5.Eop, h, h', if_false, zero_add, smul_neg]

theorem ofFn_prod_smul' : ∀ {n : ℕ} (c : Fin n → ℂ) (X : Fin n → A),
    (List.ofFn fun i => c i • X i).prod = (∏ i, c i) • (List.ofFn X).prod
  | 0, c, X => by simp
  | n + 1, c, X => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_smul' (fun i => c i.succ) (fun i => X i.succ), Fin.prod_univ_succ,
      List.ofFn_succ, List.prod_cons, smul_mul_smul_comm]

theorem qminor_Emir (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1))
    (u : ℂ) : qminor (Emir E) a b u =
      ((∏ i, ep (a i)) * (∏ i, ep (b i))) • qminor (Formalism.FourierDecayAlt.P.Qx5.Eop E) (rv ∘ a) (rv ∘ b) u := by
  unfold qminor
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Tm_Emir, ofFn_prod_smul', Function.comp_apply]
  rw [mul_smul_comm]
  congr 1
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => ep (a i))]

theorem prod_ep_sq {m : ℕ} (c : Fin m → Fin (2 * r + k + 1)) : (∏ l, ep (c l)) * (∏ l, ep (c l)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun l _ => ep_sq _

theorem rv_xR (m : ℕ) (hm : m ≤ r) : rv ∘ xR k r m hm = sR k r m hm := by
  funext l
  exact rv_eI (Fin.castLE hm l)

open scoped Classical in

theorem AAx_mirror (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : Formalism.REAL.GlRel E)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (ℓ : ℂ)
    (hsupp : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m → y a p ≠ 0 → r + k < p.val) :
    C3.AAx k r (Emir E) (fun a q => ep q * y a (rv q)) m hm (-ℓ) =
      ((∏ l : Fin m, ep (xR k r m hm l)) * (-1) ^ m) • C3.AAv k r E y m hm ℓ := by
  unfold C3.AAx C3.AAv
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv ((Equiv.refl (Fin m)).arrowCongr (Fin.revPerm : Equiv.Perm (Fin (2 * r + k + 1)))) _ _
    (fun c => ?_)
  have hB : ((Equiv.refl (Fin m)).arrowCongr (Fin.revPerm : Equiv.Perm (Fin (2 * r + k + 1)))) c = rv ∘ c := by
    funext l; simp [Equiv.arrowCongr_apply, rv]
  rw [hB]
  set Yc : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a l => y (Fin.castLE hm a) (rv (c l)) with hYc
  have hdet : (Matrix.of fun a l : Fin m => ep (c l) * y (Fin.castLE hm a) (rv (c l))).det =
      (∏ l, ep (c l)) * Yc.det := Matrix.det_mul_row _ _

  have hq : qminor (Emir E) (xR k r m hm) c (-ℓ) =
      (((∏ l, ep (xR k r m hm l)) * (∏ l, ep (c l))) * (-1) ^ m) • qminor E (rv ∘ c) (sR k r m hm) (ℓ + (m : ℂ) - 1) := by
    rw [qminor_Emir, rv_xR, Formalism.FourierDecayAlt.P.Qx5.duality hG (rv ∘ c) (sR k r m hm) (ℓ + (m : ℂ) - 1), smul_smul]
    have hp : ((m : ℂ) - 1 - (ℓ + (m : ℂ) - 1)) = -ℓ := by ring
    have hs : ((-1 : ℂ) ^ m * (-1) ^ m) = 1 := by rw [← mul_pow]; norm_num
    rw [hp, mul_assoc, hs, mul_one]
  by_cases hY : Yc.det = 0
  · have h1 : (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) ((rv ∘ c) l)).det = 0 := hY
    rw [hdet, hY, mul_zero]
    simp only [h1, zero_smul, ite_self, smul_zero]
  ·
    have hcol : ∀ l, (c l).val < r := by
      intro l
      by_contra hl
      apply hY
      apply Matrix.det_eq_zero_of_column_eq_zero l
      intro a
      simp only [hYc, Matrix.of_apply]
      by_contra hne
      have := hsupp _ _ (by simp) hne
      rw [rv_val] at this
      omega
    have hkey : ∀ l, C3.keyS k r ((rv ∘ c) l) = (c l).val := by
      intro l
      simp only [Function.comp_apply, C3.keyS, rv_val]
      rw [if_pos (by have := hcol l; omega)]
      have := (c l).isLt
      omega
    have hmono : StrictMono c ↔ StrictMono (fun l => C3.keyS k r ((rv ∘ c) l)) := by
      simp only [hkey]
      exact ⟨fun h a b hab => h hab, fun h a b hab => h hab⟩
    by_cases hS : StrictMono c
    · have hYc' : (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) ((rv ∘ c) l)).det = Yc.det := rfl
      rw [if_pos hS, if_pos (hmono.1 hS), hdet, hq, smul_smul, smul_smul, hYc']
      congr 1
      have h2 := prod_ep_sq (k := k) (r := r) c
      linear_combination ((∏ l, ep (xR k r m hm l)) * (-1) ^ m * Yc.det) * h2
    · rw [if_neg hS, if_neg (fun h => hS (hmono.2 h)), smul_zero]

theorem prod_ep_xR (m : ℕ) (hm : m ≤ r) :
    ∏ l : Fin m, ep (xR k r m hm l) = ∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ) := by
  refine Finset.prod_congr rfl fun l _ => ?_
  rfl

theorem prod_neg_one_sq (m : ℕ) : (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun l _ => ?_
  rw [← mul_pow]
  norm_num

end mirror

def HeadAlgV : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r m : ℕ) (hm : m + 2 ≤ r)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (d ℓ : ℂ),
    Formalism.REAL.GlRel E → C3.RightRuleFn k r z' E La → W.det ≠ 0 → d ≠ 0 →
    (∀ (b : Fin (m + 1)) (x : A), La (E (esI k r ⟨b, by omega⟩) (esI k r ⟨m + 1, by omega⟩) * x) =
      (d * W⁻¹ b (Fin.last m)) • La x) →
    (∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), y ⟨a, by omega⟩ q =
      if h : r + k < q.val ∧ 2 * r + k - q.val < m + 1 then W a ⟨2 * r + k - q.val, h.2⟩ else 0) →
    (∀ q : Fin (2 * r + k + 1), y ⟨m + 1, by omega⟩ q = if q.val = 2 * r + k - (m + 1) then d else 0) →
    (W.det * d)⁻¹ • La (C3.AAv k r E y (m + 2) hm ℓ) =
      W.det⁻¹ • La (C3.AAv k r E y (m + 1) (by omega) ℓ *
          (algebraMap ℂ A (ℓ + ((m + 1 : ℕ) : ℂ)) + E (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩))) -
        (d * W.det⁻¹) • La (C3.AAv k r E y m (by omega) ℓ)

theorem _root_.Formalism.FourierDecayAlt.P.head_algebra_relations_vector : HeadAlgV := by
  intro A _ _ M _ _ k r m hm z' E La y W d ℓ hG hR hW hd hL hy hyl
  set xi'' : Fin r → Fin (2 * r + k + 1) → ℂ := fun a q => ep q * y a (rv q) with hxidef
  set εv : Fin (m + 1) → ℂ := fun b => (-1 : ℂ) ^ (b : ℕ) with hεv
  set Z'' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := W * Matrix.diagonal εv with hZdef
  have hεsq : ∀ b, εv b * εv b = 1 := by intro b; simp only [hεv]; rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hDinv : (Matrix.diagonal εv)⁻¹ = Matrix.diagonal εv := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; simp [Matrix.diagonal_apply, hεsq, Matrix.one_apply]
  have hDdet : (Matrix.diagonal εv).det = ∏ b : Fin (m + 1), εv b := Matrix.det_diagonal
  have hZdet : Z''.det = W.det * ∏ b : Fin (m + 1), εv b := by rw [hZdef, Matrix.det_mul, hDdet]
  have hεne : (∏ b : Fin (m + 1), εv b) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun b _ => by
    simp only [hεv]; exact pow_ne_zero _ (by norm_num))
  have hZ : Z''.det ≠ 0 := by rw [hZdet]; exact mul_ne_zero hW hεne
  have hZinv : ∀ b, Z''⁻¹ b (Fin.last m) = εv b * W⁻¹ b (Fin.last m) := by
    intro b
    have hWu : IsUnit W.det := isUnit_iff_ne_zero.2 hW
    have hDu : IsUnit (Matrix.diagonal εv).det := isUnit_iff_ne_zero.2 (by rw [hDdet]; exact hεne)
    rw [hZdef, Matrix.mul_inv_rev, hDinv, Matrix.diagonal_mul]
  set c : ℂ := (-1 : ℂ) ^ (m + 1) * d with hcdef
  set c' : ℂ := -((-1 : ℂ) ^ (m + 1) * d) with hc'def
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hd

  have hR'' : ∀ (x : A) (p q : Fin (2 * r + k + 1)), p.val < q.val → q.val < r →
      La (x * Emir E p q) = (if q.val = p.val + 1 then (1 : ℂ) else 0) • La x := by
    intro x p q hpq hqr
    have hin : C3.InNp k r (rv q) (rv p) := by
      unfold C3.InNp; rw [rv_val, rv_val]; omega
    unfold Emir
    rw [mul_neg, mul_smul_comm, map_neg, map_smul, hR x _ _ hin]
    have hdp : C3.dpsiP k r z' (rv q) (rv p) = if q.val = p.val + 1 then 1 else 0 := by
      unfold C3.dpsiP
      rw [rv_val, rv_val]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      by_cases h : q.val = p.val + 1
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    rw [hdp]
    by_cases h : q.val = p.val + 1
    · simp only [if_pos h, one_smul]
      have : ep p * ep q = -1 := by
        unfold ep; rw [h, pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
      rw [this, neg_one_smul, neg_neg]
    · simp only [if_neg h, zero_smul, smul_zero, neg_zero]
  have hepI : ∀ (b : ℕ) (hb : b < r), ep (eI k r ⟨b, hb⟩) = (-1 : ℂ) ^ b := by intro b hb; simp [ep, eI]
  have hL'' : ∀ (b : Fin (m + 1)) (x : A), La (Emir E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨b, by omega⟩) * x) =
      (c' * Z''⁻¹ b (Fin.last m)) • La x := by
    intro b x
    unfold Emir
    rw [neg_mul, smul_mul_assoc, map_neg, map_smul, rv_eI, rv_eI, hL b x, hZinv b, smul_smul, hepI, hepI]
    rw [← neg_smul]
    congr 1
    simp only [hc'def, hεv]
    ring
  have hxi'' : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), xi'' ⟨a, by omega⟩ q =
      if h : q.val < m + 1 then Z'' a ⟨q, h⟩ else 0 := by
    intro a q
    simp only [hxidef]
    rw [hy a (rv q)]
    by_cases hq : q.val < m + 1
    · rw [dif_pos (by rw [rv_val]; omega), dif_pos hq, hZdef, Matrix.mul_diagonal]
      have e1 : (⟨2 * r + k - (rv q).val, by rw [rv_val]; omega⟩ : Fin (m + 1)) = ⟨q.val, hq⟩ :=
        Fin.ext (by simp only; rw [rv_val]; omega)
      rw [e1]
      simp only [hεv, ep]
      ring
    · rw [dif_neg (by rw [rv_val]; omega), dif_neg hq, mul_zero]
  have hxl'' : ∀ q : Fin (2 * r + k + 1), xi'' ⟨m + 1, by omega⟩ q = if q.val = m + 1 then c else 0 := by
    intro q
    simp only [hxidef]
    rw [hyl (rv q)]
    by_cases hq : q.val = m + 1
    · rw [if_pos (by rw [rv_val]; omega), if_pos hq, hcdef]
      simp only [ep, hq]
    · rw [if_neg (by rw [rv_val]; omega), if_neg hq, mul_zero]
  have hmain := headAlg_gen A M k r m hm (Emir E) La xi'' Z'' c c' (-ℓ) (Emir_gl hG) hR'' hZ hc hL'' hxi'' hxl''
  have hsupp : ∀ m' : ℕ, m' ≤ m + 2 → ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m' → y a p ≠ 0 →
      r + k < p.val := by
    intro m' hm' a p ha hne
    by_cases h1 : a.val < m + 1
    · have e : a = ⟨((⟨a.val, h1⟩ : Fin (m + 1)) : ℕ), by omega⟩ := Fin.ext rfl
      rw [e, hy] at hne
      split_ifs at hne with hc0
      · exact hc0.1
      · exact absurd rfl hne
    · have e : a = ⟨m + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, hyl] at hne
      split_ifs at hne with hc0
      · omega
      · exact absurd rfl hne
  simp only [hxidef] at hmain
  rw [AAx_mirror E hG y (m + 2) hm ℓ (hsupp _ le_rfl), AAx_mirror E hG y (m + 1) _ ℓ (hsupp _ (by omega)),
    AAx_mirror E hG y m _ ℓ (hsupp _ (by omega))] at hmain
  have hEd : Emir E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) =
      -E (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩) := by
    unfold Emir; rw [ep_sq, one_smul, rv_eI]
  have hal : algebraMap ℂ A (-ℓ - ((m + 1 : ℕ) : ℂ)) = -algebraMap ℂ A (ℓ + ((m + 1 : ℕ) : ℂ)) := by
    rw [← map_neg]; congr 1; ring
  rw [hEd, hal, ← neg_add, mul_neg, map_neg, smul_mul_assoc, map_smul, map_smul, map_smul] at hmain
  simp only [prod_ep_xR] at hmain
  rw [hZdet] at hmain
  have hPe : (∏ b : Fin (m + 1), εv b) = (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (-1) ^ m := by
    simp only [hεv]; rw [Fin.prod_univ_castSucc]; simp
  have hP1 : (∏ l : Fin (m + 1), (-1 : ℂ) ^ (l : ℕ)) = (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (-1) ^ m := by
    rw [Fin.prod_univ_castSucc]; simp
  have hP2 : (∏ l : Fin (m + 2), (-1 : ℂ) ^ (l : ℕ)) =
      (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (-1) ^ m * (-1) ^ (m + 1) := by
    rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]; rw [hP1]
  rw [hPe, hP2] at hmain
  try rw [hP1] at hmain
  set P0 := ∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ) with hP0
  set e := (-1 : ℂ) ^ m with he
  have hP0sq : P0 * P0 = 1 := prod_neg_one_sq m
  have hesq : e * e = 1 := by rw [he, ← mul_pow]; norm_num
  have hP0ne : P0 ≠ 0 := fun h => by rw [h, zero_mul] at hP0sq; exact zero_ne_one hP0sq
  have hene : e ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm1 : (-1 : ℂ) ^ (m + 1) = -e := by rw [pow_succ, he]; ring
  have hm2 : (-1 : ℂ) ^ (m + 2) = e := by rw [pow_add, he]; norm_num
  rw [hcdef, hc'def] at hmain
  try simp only [hm1, hm2] at hmain
  set V2 := La (C3.AAv k r E y (m + 2) hm ℓ) with hV2
  set V1 := La (C3.AAv k r E y (m + 1) (by omega) ℓ *
    (algebraMap ℂ A (ℓ + ((m + 1 : ℕ) : ℂ)) + E (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩))) with hV1
  set V0 := La (C3.AAv k r E y m (by omega) ℓ) with hV0
  rw [smul_smul, smul_neg, smul_smul, smul_smul, ← neg_smul] at hmain
  have e1 : ((W.det * (P0 * e)) * (-e * d))⁻¹ * (P0 * e * -e * e) = e * (W.det * d)⁻¹ := by
    field_simp
  have e2 : -((W.det * (P0 * e))⁻¹ * (P0 * e * -e)) = e * W.det⁻¹ := by
    field_simp
  have e3 : -(-e * d) * (W.det * (P0 * e))⁻¹ * (P0 * e) = e * (d * W.det⁻¹) := by
    field_simp
  rw [e1, e2, e3, ← smul_smul, ← smul_smul, ← smul_smul, ← smul_sub] at hmain
  exact smul_right_injective M hene hmain

end Formalism.FourierDecayAlt.P.PBG
