import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
import Formalism.HermitianCurvature.StatementC
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Carrier.WtDet

variable {N : ℕ}

theorem mono_eq (π : Fin N → Fin N) (hπ : ∀ a, π (π a) = a) (c : Fin N → ℂ) :
    Formalism.L2.SG.PtCell.mono π c =
      Matrix.diagonal c * (Function.Involutive.toPerm π hπ).permMatrix ℂ := by
  ext a b
  by_cases h : b = π a
  · subst h
    simp [Formalism.L2.SG.PtCell.mono, Matrix.diagonal_mul, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Function.Involutive.coe_toPerm]
    exact fun e => absurd rfl e
  · have h' : ¬ π a = b := fun e => h e.symm
    simp [Formalism.L2.SG.PtCell.mono, Matrix.diagonal_mul, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Function.Involutive.coe_toPerm, h, h']
    exact fun e => absurd e h'

theorem norm_det_mono (π : Fin N → Fin N) (hπ : ∀ a, π (π a) = a) (c : Fin N → ℂ) :
    ‖(Formalism.L2.SG.PtCell.mono π c).det‖ = ∏ a, ‖c a‖ := by
  rw [mono_eq π hπ c, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation, norm_mul, norm_prod]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Function.Involutive.toPerm π hπ)) with h | h <;> simp [h]

theorem norm_det_sub_mono (π : Fin N → Fin N) (hπ : ∀ a, π (π a) = a) (c : Fin N → ℂ) {l : ℕ} (hl : l ≤ N)
    (hπl : ∀ a : Fin N, a.val < l → (π a).val < l) :
    ‖((Formalism.L2.SG.PtCell.mono π c).submatrix (Fin.castLE hl) (Fin.castLE hl)).det‖ =
      ∏ a : Fin l, ‖c (Fin.castLE hl a)‖ := by
  have hsub : (Formalism.L2.SG.PtCell.mono π c).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Formalism.L2.SG.PtCell.mono (fun a : Fin l => (⟨(π (Fin.castLE hl a)).val, hπl _ a.2⟩ : Fin l))
        (fun a => c (Fin.castLE hl a)) := by
    ext a b
    simp only [Formalism.L2.SG.PtCell.mono, Matrix.submatrix_apply, Fin.ext_iff, Fin.coe_castLE]
  rw [hsub, norm_det_mono _ (fun a => Fin.ext (by
    show (π (Fin.castLE hl _)).val = a.val
    rw [show Fin.castLE hl (⟨(π (Fin.castLE hl a)).val, hπl _ a.2⟩ : Fin l) = π (Fin.castLE hl a) from Fin.ext rfl,
      hπ]
    rfl))]

theorem det_sub_mono_zero (π : Fin N → Fin N) (c : Fin N → ℂ) {l : ℕ} (hl : l ≤ N) (a0 : Fin N) (ha0 : a0.val < l)
    (hπ0 : l ≤ (π a0).val) :
    ((Formalism.L2.SG.PtCell.mono π c).submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (⟨a0.val, ha0⟩ : Fin l)
  intro b
  simp only [Formalism.L2.SG.PtCell.mono, Matrix.submatrix_apply]
  rw [if_neg]
  intro h
  have h1 := congrArg Fin.val h
  rw [show Fin.castLE hl (⟨a0.val, ha0⟩ : Fin l) = a0 from Fin.ext rfl] at h1
  simp only [Fin.coe_castLE] at h1
  have hb := b.2
  omega

section Lists

variable {K : Type*} [Field K]

open Formalism.L2.SG.PtCell

theorem pperm_append : ∀ (L1 L2 : List (K × ℕ)) (i : ℕ),
    pperm (L1 ++ L2) i = if i < (L1.map Prod.snd).sum then pperm L1 i else (L1.map Prod.snd).sum + pperm L2 (i - (L1.map Prod.snd).sum)
  | [], L2, i => by simp [pperm]
  | (t, s) :: L1, L2, i => by
    simp only [List.cons_append, pperm, List.map_cons, List.sum_cons]
    by_cases h1 : i < s
    · rw [if_pos h1, if_pos (by omega), if_pos h1]
    · rw [if_neg h1, pperm_append L1 L2 (i - s)]
      by_cases h2 : i - s < (L1.map Prod.snd).sum
      · rw [if_pos h2, if_pos (by omega), if_neg h1]
      · rw [if_neg h2, if_neg (by omega), show i - s - (L1.map Prod.snd).sum = i - (s + (L1.map Prod.snd).sum) by omega]
        ring

theorem pval_append : ∀ (L1 L2 : List (K × ℕ)) (i : ℕ),
    pval (L1 ++ L2) i = if i < (L1.map Prod.snd).sum then pval L1 i else pval L2 (i - (L1.map Prod.snd).sum)
  | [], L2, i => by simp [pval]
  | (t, s) :: L1, L2, i => by
    simp only [List.cons_append, pval, List.map_cons, List.sum_cons]
    by_cases h1 : i < s
    · rw [if_pos h1, if_pos (by omega), if_pos h1]
    · rw [if_neg h1, pval_append L1 L2 (i - s)]
      by_cases h2 : i - s < (L1.map Prod.snd).sum
      · rw [if_pos h2, if_pos (by omega), if_neg h1]
      · rw [if_neg h2, if_neg (by omega), show i - s - (L1.map Prod.snd).sum = i - (s + (L1.map Prod.snd).sum) by omega]

theorem prod_pval : ∀ (L : List (ℂ × ℕ)),
    ∏ i ∈ Finset.range (L.map Prod.snd).sum, ‖pval L i‖ = (L.map fun b => ‖b.1‖ ^ b.2).prod
  | [] => by simp
  | (t, s) :: L => by
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    rw [Finset.prod_range_add, ← prod_pval L]
    congr 1
    · rw [Finset.prod_congr rfl (fun i hi => by rw [show pval ((t, s) :: L) i = t by
        simp [pval, Finset.mem_range.mp hi]]), Finset.prod_const, Finset.card_range]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [pval]

theorem norm_det_ptMat {N : ℕ} (γ : Formalism.MainNotions.S.Point ℂ N) :
    ‖(Formalism.MainNotions.S.ptMat γ).det‖ = (γ.1.map fun b => ‖b.1‖ ^ b.2).prod := by
  have hinv : ∀ a, pinv γ (pinv γ a) = a := fun a =>
    Fin.ext (pperm_pperm γ.1 (fun b hb => (γ.2.1 b hb).2) a.val (by rw [γ.2.2]; exact a.isLt))
  rw [ptMat_eq_mono, norm_det_mono _ hinv, Fin.prod_univ_eq_prod_range (fun i => ‖pval γ.1 i‖) N]
  have h := prod_pval γ.1
  rw [γ.2.2] at h
  exact h

theorem norm_leadMinor_one {r : ℕ} (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (L1 : List (ℂ × ℕ)) (c : ℂ)
    (h : γ.1 = L1 ++ [(c, 1)]) :
    ‖Formalism.MainNotions.S.leadMinor (Formalism.MainNotions.S.ptMat γ) r (Nat.le_succ r)‖ = (L1.map fun b => ‖b.1‖ ^ b.2).prod := by
  have hS : (L1.map Prod.snd).sum = r := by
    have := γ.2.2
    rw [h] at this
    simpa using this
  have hpos1 : ∀ b ∈ L1, 1 ≤ b.2 := fun b hb => (γ.2.1 b (by rw [h]; exact List.mem_append_left _ hb)).2
  have hinv : ∀ a, pinv γ (pinv γ a) = a := fun a =>
    Fin.ext (pperm_pperm γ.1 (fun b hb => (γ.2.1 b hb).2) a.val (by rw [γ.2.2]; exact a.isLt))
  have hcl : ∀ a : Fin (r + 1), a.val < r → (pinv γ a).val < r := by
    intro a ha
    show pperm γ.1 a.val < r
    rw [h, pperm_append, if_pos (by omega)]
    have := pperm_lt L1 hpos1 a.val (by omega)
    omega
  unfold Formalism.MainNotions.S.leadMinor
  rw [ptMat_eq_mono, norm_det_sub_mono (pinv γ) hinv _ (Nat.le_succ r) hcl]
  simp only [Fin.coe_castLE]
  rw [Fin.prod_univ_eq_prod_range (fun i => ‖pval γ.1 i‖) r]
  have hv : ∀ i ∈ Finset.range r, ‖pval γ.1 i‖ = ‖pval L1 i‖ := by
    intro i hi
    rw [h, pval_append, if_pos (by rw [hS]; exact Finset.mem_range.1 hi)]
  rw [Finset.prod_congr rfl hv, ← hS, prod_pval]

theorem leadMinor_big {r : ℕ} (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (L1 : List (ℂ × ℕ)) (c : ℂ) (s : ℕ) (hs : 2 ≤ s)
    (h : γ.1 = L1 ++ [(c, s)]) : Formalism.MainNotions.S.leadMinor (Formalism.MainNotions.S.ptMat γ) r (Nat.le_succ r) = 0 := by
  have hS : (L1.map Prod.snd).sum + s = r + 1 := by
    have := γ.2.2
    rw [h] at this
    simpa using this
  unfold Formalism.MainNotions.S.leadMinor
  rw [ptMat_eq_mono]
  apply det_sub_mono_zero _ _ (Nat.le_succ r) (⟨(L1.map Prod.snd).sum, by omega⟩ : Fin (r + 1))
    (by show (L1.map Prod.snd).sum < r; omega)
  show r ≤ pperm γ.1 (L1.map Prod.snd).sum
  rw [h, pperm_append, if_neg (lt_irrefl _), Nat.sub_self]
  simp only [pperm, if_pos (show 0 < s by omega)]
  omega

end Lists

section Weights

def FA (k r : ℕ) (GG : ℝ) : ℕ → List (ℂ × ℕ) → ℝ
  | _, [] => 1
  | b, (c, s) :: R => (if b + s - 1 = r + 1 ∧ s = 1 then GG ^ (k - 1)
      else ‖c‖ ^ (2 * (s : ℤ) * (Formalism.FourierDecayAlt.C.Mlev k r (b + s - 1) + s - 3))) * FA k r GG (b + s) R

def FH (r : ℕ) : ℕ → List (ℂ × ℕ) → ℝ
  | _, [] => 1
  | b, (c, s) :: R => ‖c‖ ^ (2 * s * (2 * (r + 1 - (b + s - 1)) + s - 1)) * FH r (b + s) R

theorem FA_append (k r : ℕ) (GG : ℝ) : ∀ (L1 L2 : List (ℂ × ℕ)) (b : ℕ),
    FA k r GG b (L1 ++ L2) = FA k r GG b L1 * FA k r GG (b + (L1.map Prod.snd).sum) L2
  | [], L2, b => by simp [FA]
  | (c, s) :: L1, L2, b => by
    simp only [List.cons_append, FA, FA_append k r GG L1 L2 (b + s), List.map_cons, List.sum_cons, add_assoc, mul_assoc]

theorem FH_append (r : ℕ) : ∀ (L1 L2 : List (ℂ × ℕ)) (b : ℕ),
    FH r b (L1 ++ L2) = FH r b L1 * FH r (b + (L1.map Prod.snd).sum) L2
  | [], L2, b => by simp [FH]
  | (c, s) :: L1, L2, b => by
    simp only [List.cons_append, FH, FH_append r L1 L2 (b + s), List.map_cons, List.sum_cons, add_assoc, mul_assoc]

theorem FA_pre (k r : ℕ) (hk : 1 ≤ k) (GG : ℝ) : ∀ (L : List (ℂ × ℕ)) (b : ℕ), 1 ≤ b →
    b + (L.map Prod.snd).sum ≤ r + 1 → (∀ x ∈ L, 1 ≤ x.2) →
    FA k r GG b L = FH r b L * (L.map fun x => ‖x.1‖ ^ x.2).prod ^ (2 * (k - 1))
  | [], _, _, _, _ => by simp [FA, FH]
  | (c, s) :: L, b, hb, hs, hL => by
    simp only [List.map_cons, List.sum_cons] at hs
    have hs1 : 1 ≤ s := hL (c, s) (by simp)
    have ih := FA_pre k r hk GG L (b + s) (by omega) (by omega) (fun x hx => hL x (by simp [hx]))
    simp only [FA, FH, List.map_cons, List.prod_cons, ih]
    rw [if_neg (by omega)]
    have he : (2 * (s : ℤ) * (Formalism.FourierDecayAlt.C.Mlev k r (b + s - 1) + s - 3)) =
        ((2 * s * (2 * (r + 1 - (b + s - 1)) + s - 1) + s * (2 * (k - 1)) : ℕ) : ℤ) := by
      obtain ⟨d, hd⟩ : ∃ d, r + 1 = (b + s - 1) + d := ⟨r + 1 - (b + s - 1), by omega⟩
      have e1 : r + 1 - (b + s - 1) = d := by omega
      have e3 : ((r : ℤ) + 1 - ((b + s - 1 : ℕ) : ℤ)) = d := by
        have := congrArg (fun x : ℕ => (x : ℤ)) hd
        push_cast at this
        linarith
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      unfold Formalism.FourierDecayAlt.C.Mlev
      rw [e3, e1, show 2 * d + (s' + 1) - 1 = 2 * d + s' by omega, show k' + 1 - 1 = k' by omega]
      push_cast
      ring
    rw [he, zpow_natCast, pow_add, mul_pow, ← pow_mul]
    ring

theorem core_wt (k r : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (q : Formalism.MainNotions.S.Point ℂ (r + 1)) (L1 : List (ℂ × ℕ)) (c : ℂ) (s : ℕ)
    (h : q.1 = L1 ++ [(c, s)]) (GG : ℝ) (hGG : s = 1 → GG = ‖c‖ ^ 2 - T * T') :
    Formalism.MainNotions.S.ThB.Gpt T T' q ^ (k - 1) * FH r 1 q.1 = FA k r GG 1 q.1 := by
  have hsum : (L1.map Prod.snd).sum + s = r + 1 := by
    have := q.2.2
    rw [h] at this
    simpa using this
  have hpos1 : ∀ x ∈ L1, 1 ≤ x.2 := fun x hx => (q.2.1 x (by rw [h]; exact List.mem_append_left _ hx)).2
  have hs : 1 ≤ s := (q.2.1 (c, s) (by rw [h]; simp)).2
  have hFA : FA k r GG 1 q.1 = FH r 1 L1 * (L1.map fun x => ‖x.1‖ ^ x.2).prod ^ (2 * (k - 1)) *
      FA k r GG (1 + (L1.map Prod.snd).sum) [(c, s)] := by
    rw [h, FA_append, FA_pre k r hk GG L1 1 le_rfl (by omega) hpos1]
  have hFH : FH r 1 q.1 = FH r 1 L1 * FH r (1 + (L1.map Prod.snd).sum) [(c, s)] := by rw [h, FH_append]
  have hD : ‖(Formalism.MainNotions.S.ptMat q).det‖ = (L1.map fun x => ‖x.1‖ ^ x.2).prod * ‖c‖ ^ s := by
    rw [norm_det_ptMat, h, List.map_append, List.prod_append]
    simp
  have hfull : Formalism.MainNotions.S.leadMinor (Formalism.MainNotions.S.ptMat q) (r + 1) le_rfl = (Formalism.MainNotions.S.ptMat q).det := by
    have hid : (Fin.castLE (le_refl (r + 1))) = id := funext fun a => Fin.ext rfl
    simp only [Formalism.MainNotions.S.leadMinor, hid, Matrix.submatrix_id_id]
  have hr0 : r + 1 - (1 + (L1.map Prod.snd).sum + s - 1) = 0 := by omega
  have hlast : 1 + (L1.map Prod.snd).sum + s - 1 = r + 1 := by omega
  simp only [Formalism.MainNotions.S.ThB.Gpt, hfull, Complex.normSq_eq_norm_sq, hD]
  rw [hFA, hFH]
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · have hs1 : s = 1 := by omega
    subst hs1
    have hFA1 : FA k r GG (1 + (L1.map Prod.snd).sum) [(c, 1)] = (‖c‖ ^ 2 - T * T') ^ (k - 1) := by
      simp only [FA]
      rw [if_pos (by refine ⟨hlast, ?_⟩; trivial), hGG rfl, mul_one]
    have hFH1 : FH r (1 + (L1.map Prod.snd).sum) [(c, 1)] = 1 := by
      simp only [FH]
      rw [hr0]
      simp
    rw [hFA1, hFH1, norm_leadMinor_one q L1 c h]
    have hb : ((L1.map fun x => ‖x.1‖ ^ x.2).prod * ‖c‖ ^ 1) ^ 2 - T * T' * (L1.map fun x => ‖x.1‖ ^ x.2).prod ^ 2 =
        (L1.map fun x => ‖x.1‖ ^ x.2).prod ^ 2 * (‖c‖ ^ 2 - T * T') := by ring
    rw [hb, mul_pow, ← pow_mul]
    ring
  · rw [leadMinor_big q L1 c s hs2 h]
    have hx : ‖c‖ ^ (2 * (s : ℤ) * (Formalism.FourierDecayAlt.C.Mlev k r (r + 1) + s - 3)) =
        ‖c‖ ^ (2 * s * (2 * 0 + s - 1)) * (‖c‖ ^ s) ^ (2 * (k - 1)) := by
      rw [← pow_mul, ← pow_add, ← zpow_natCast]
      congr 1
      have h2 : 1 ≤ 2 * 0 + s := by omega
      simp only [Formalism.FourierDecayAlt.C.Mlev]
      zify [h2, hk]
      push_cast
      ring
    have hFA2 : FA k r GG (1 + (L1.map Prod.snd).sum) [(c, s)] =
        ‖c‖ ^ (2 * s * (2 * 0 + s - 1)) * (‖c‖ ^ s) ^ (2 * (k - 1)) := by
      simp only [FA]
      rw [if_neg (by omega), hlast, hx, mul_one]
    have hFH2 : FH r (1 + (L1.map Prod.snd).sum) [(c, s)] = ‖c‖ ^ (2 * s * (2 * 0 + s - 1)) := by
      simp only [FH]
      rw [hr0, mul_one]
    rw [hFA2, hFH2]
    simp only [norm_zero]
    ring

end Weights

end Formalism.L2.SG.Pf.Carrier.WtDet
