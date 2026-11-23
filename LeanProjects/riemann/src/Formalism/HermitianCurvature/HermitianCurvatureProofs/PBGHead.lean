import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem mono_omit {k r m : ℕ} (hm : m + 1 ≤ r) (c : Fin m → Fin (2 * r + k + 1)) (hc : StrictMono c)
    (hlt : ∀ l, (c l).val < m + 1) : ∃ l0 : Fin (m + 1), c = xR k r (m + 1) hm ∘ l0.succAbove := by
  have hex : ∃ l0 : Fin (m + 1), ∀ l, (c l).val ≠ l0.val := by
    by_contra hne
    push Not at hne
    choose f hf using hne
    have hinj : Function.Injective f := by
      intro a b hab
      apply Fin.ext
      have := hf a; have := hf b; rw [hab] at *; omega
    have := Fintype.card_le_of_injective f hinj
    simp at this
  obtain ⟨l0, hl0⟩ := hex
  refine ⟨l0, ?_⟩
  apply uniq_mono _ _ ?_ hc
  · intro l
    have h1 : (⟨(c l).val, hlt l⟩ : Fin (m + 1)) ≠ l0 := by
      intro h; apply hl0 l; rw [← h]
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h1
    refine ⟨j, ?_⟩
    ext
    simp only [Function.comp_apply, xR, eI, Fin.val_castLE]
    rw [hj]
  · exact (fun a b hab => by simp only [Function.comp_apply, xR, eI]; exact Fin.strictMono_succAbove l0 hab)

theorem omit_inj {k r m : ℕ} (hm : m + 1 ≤ r) :
    Function.Injective (fun l0 : Fin (m + 1) => xR k r (m + 1) hm ∘ l0.succAbove) := by
  intro l0 l1 h
  apply Fin.succAbove_left_injective
  funext l
  have h2 := congrArg Fin.val (congrFun h l)
  exact Fin.ext (by simpa [C3.xR, eI] using h2)

theorem AAx_omit {A : Type} [Ring A] [Algebra ℂ A] (k r m : ℕ) (hm : m + 1 ≤ r)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (u : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m → m + 1 ≤ p.val → xi a p = 0) :
    AAx k r E xi m (by omega) u = ∑ l0 : Fin (m + 1),
      (Matrix.of fun a l : Fin m => xi (Fin.castLE (by omega) a) (xR k r (m + 1) hm (l0.succAbove l))).det •
        qminor E (xR k r m (by omega)) (xR k r (m + 1) hm ∘ l0.succAbove) u := by
  classical
  unfold AAx
  set g := fun l0 : Fin (m + 1) => xR k r (m + 1) hm ∘ l0.succAbove
  have hg : Function.Injective g := omit_inj hm
  have hsub : Finset.image g Finset.univ ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image (fun a _ b _ h => hg h)]
    apply Finset.sum_congr rfl
    intro l0 _
    rw [if_pos]
    · rfl
    · intro a b hab; simp only [g, Function.comp_apply, xR, eI]; exact Fin.strictMono_succAbove l0 hab
  · intro c _ hc
    split_ifs with hP
    · by_cases hS : ∀ l, (c l).val < m + 1
      · obtain ⟨l0, hl0⟩ := mono_omit hm c hP hS
        exact absurd (Finset.mem_image.2 ⟨l0, Finset.mem_univ _, hl0.symm⟩) hc
      · push Not at hS
        obtain ⟨l, hl⟩ := hS
        rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by
          simp only [Matrix.of_apply]; exact hz _ _ (by simp) hl), zero_smul]
    · rfl

theorem inv_last {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hZ : Z.det ≠ 0) (b : Fin (m + 1)) :
    Z⁻¹ b (Fin.last m) = Z.det⁻¹ * ((-1) ^ (m + (b : ℕ)) * (Z.submatrix Fin.castSucc b.succAbove).det) := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, Fin.val_last,
    smul_eq_mul, Ring.inverse_eq_inv']

theorem _root_.Formalism.FourierDecayAlt.P.head_algebra_relations : Formalism.FourierDecayAlt.KB.HeadAlg := by
  intro A _ _ M _ _ k r m hm z' E La xi Z c u hG hR hZ hc hL hxi hxl
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
      rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
      have : dpsiP k r z' (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))) = 0 := by
        unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
      rw [this, zero_smul, smul_zero]
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
      rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
      have : dpsiP k r z' (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1))) = 1 := by
        unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
      rw [this, one_smul]
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
      ∑ l : Fin (m + 1), ((-1 : ℂ) ^ (m + (l : ℕ)) * (c * Z⁻¹ l (Fin.last m))) •
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
  linear_combination (c * Z.det⁻¹ * (Z.submatrix Fin.castSucc l.succAbove).det) * hs

end Formalism.FourierDecayAlt.P.PBG
