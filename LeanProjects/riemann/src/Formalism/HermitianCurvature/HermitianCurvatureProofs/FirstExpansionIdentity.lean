import Formalism.HermitianCurvature.HermitianCurvatureProofs.AAvCongr

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem keyS_inj (k r : ℕ) : Function.Injective (keyS k r) := by
  intro p q hpq
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  unfold keyS at hpq
  split_ifs at hpq <;> omega

theorem keyS_esI (k r : ℕ) (x : Fin r) : keyS k r (esI k r x) = x.val := by
  have hx := x.isLt
  have c : r + k < 2 * r + k - x.val := by omega
  simp only [keyS, Formalism.QuantumDeterminants.esI, c, if_true]
  omega

theorem star_sgnW (m : ℕ) : star (sgnW m) = sgnW m := by
  simp [sgnW]

theorem neg_one_sq' (s : ℕ) : ((-1 : ℂ) ^ s) * ((-1) ^ s) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem zb_col_zero (i0 s' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (a : ℕ) (ha : a < i0 + s') :
    Zb i0 (s' + 1) h t a i0 = 0 := by
  unfold Zb
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

theorem first_expansion_identity : ExpansionOmittedColumn := by
  intro A _ _ M _ _ k r z' E La xi i0 s h t u hs hj hR hdet ht hxi
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  rw [AAx_congr k r E xi (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm u]
  have hhead : AAx k r E xi i0 (by omega) u =
      h.det • qminor E (xR k r i0 (by omega)) (xR k r i0 (by omega)) u := by
    apply AAx_head
    · intro a p ha hp
      rw [hxi a p (by omega)]
      split_ifs with hp'
      · unfold Zb
        rw [dif_pos ha, dif_neg (by omega)]
      · rfl
    · intro a b
      have ha := a.isLt
      have hb := b.isLt
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp [Zb, xR, Formalism.QuantumDeterminants.eI, ha, hb]
  have he : StrictMono (fun l : Fin (i0 + s') =>
      xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) := by
    intro a b hab
    have := (Fin.strictMono_succAbove (⟨i0, by omega⟩ : Fin (i0 + s' + 1))) hab
    rw [Fin.lt_def] at this ⊢
    simpa [xR, Formalism.QuantumDeterminants.eI] using this
  have hmain : AAx k r E xi (i0 + s') hm u = (h.det * t ^ s' * sgnW s') •
      qminor E (xR k r (i0 + s') hm)
        (fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) u := by
    classical
    have hX : ∀ (a : Fin (i0 + s')) (p : Fin (2 * r + k + 1)),
        p ∉ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} → xi (Fin.castLE hm a) p = 0 := by
      intro a p hp
      simp only [Set.mem_setOf_eq, not_and, not_not] at hp
      have ha := a.isLt
      rw [hxi _ p (by simp only [Fin.coe_castLE]; omega)]
      split_ifs with hp1
      · rw [hp (by omega)]
        exact zb_col_zero i0 s' h t _ (by simp only [Fin.coe_castLE]; omega)
      · rfl
    have hu : ∀ c : Fin (i0 + s') → Fin (2 * r + k + 1), StrictMono c →
        (∀ l, c l ∈ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0}) →
        c = fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) := by
      intro c hc hS
      apply uniq_mono _ _ he hc
      intro l
      obtain ⟨h1, h2⟩ := hS l
      have hne : (⟨(c l).val, h1⟩ : Fin (i0 + s' + 1)) ≠ ⟨i0, by omega⟩ := fun e => h2 (congrArg Fin.val e)
      obtain ⟨j, hj'⟩ := Fin.exists_succAbove_eq hne
      refine ⟨j, ?_⟩
      apply Fin.ext
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, hj']
    have hs := sum_single (M := A) StrictMono (fun a p => xi (Fin.castLE hm a) p)
      {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} hX _ he hu
      (fun c => qminor E (xR k r (i0 + s') hm) c u)
    have hdet' : (Matrix.of fun a l : Fin (i0 + s') => xi (Fin.castLE hm a)
        (xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l))).det =
        h.det * t ^ s' * sgnW s' := by
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp]
      congr 1
      ext a l
      have ha := a.isLt
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      simp only [Matrix.of_apply]
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]
    unfold AAx
    rw [← hdet']
    convert hs using 1
  have hpeel := first_peeling_identity A k r z' E (i0 + s') (by omega) ⟨i0, by omega⟩ u
  have hL := la_congr hR hpeel
  have hsc : (h.det * t ^ (s' + 1) * sgnW (s' + 1))⁻¹ * (h.det * t ^ s' * sgnW s') =
      (-1 : ℂ) ^ (s' + 1 - 1) * t⁻¹ * (h.det⁻¹ * h.det) := by
    rw [sgnW_succ', Nat.add_sub_cancel, scal_E _ _ _ _ s' hdet ht (sgnW_sq s') (neg_one_sq' s')]
  rw [hmain, hhead, map_smul, map_smul, hL, (derivative_leading_zb i0 (s' + 1) h t).2,
    (derivative_leading_zb i0 (s' + 1) h t).1, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [hsc]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
