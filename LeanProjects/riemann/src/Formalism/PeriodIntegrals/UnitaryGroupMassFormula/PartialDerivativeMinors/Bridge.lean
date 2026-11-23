import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

namespace Br

variable {H : Type} {N0 N1 : ℕ}

abbrev zF (t : H) (a : Fin N0) (b : Fin N1) : ZV H N0 N1 := ((false, t), a, b)

abbrev zT (t : H) (a : Fin N0) (b : Fin N1) : ZV H N0 N1 := ((true, t), a, b)

abbrev up (κ : ZV H N0 N1 →₀ ℕ) (t : H) (a : Fin N0) (b : Fin N1) : ZV H N0 N1 →₀ ℕ :=
  κ + Finsupp.single (zF t a b) 1 + Finsupp.single (zT t a b) 1

private theorem coeff_pd_eq_coeff_add_single_mul (i : XZ (Bool × H) N0 N1) (Q : PolyXZ H N0 N1) (ν : XZ (Bool × H) N0 N1 →₀ ℕ) :
    MvPolynomial.coeff ν (pd i Q) = MvPolynomial.coeff (ν + Finsupp.single i 1) Q * ((ν i : ℤ) + 1) := by
  show MvPolynomial.coeff ν (MvPolynomial.pderiv i Q) = _
  refine MvPolynomial.induction_on' Q (fun s c => ?_) (fun p q hp hq => ?_)
  · rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases h : s = ν + Finsupp.single i 1
    · subst h
      rw [if_pos (add_tsub_cancel_right _ _), if_pos rfl]
      simp
    · rw [if_neg h, zero_mul]
      by_cases h2 : s - Finsupp.single i 1 = ν
      · rw [if_pos h2]
        have hsi : s i = 0 := by
          by_contra hne
          apply h
          rw [← h2]
          ext j
          simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
          split_ifs with hj
          · subst hj; omega
          · omega
        simp [hsi]
      · rw [if_neg h2]
  · simp only [map_add, MvPolynomial.coeff_add, hp, hq, add_mul]

theorem coeff_lapT (t : H) (Q : PolyXZ H N0 N1) (ν : XZ (Bool × H) N0 N1 →₀ ℕ) :
    MvPolynomial.coeff ν (lapT N0 N1 t Q) =
      ∑ a : Fin N0, ∑ b : Fin N1,
        MvPolynomial.coeff (ν + Finsupp.single (Sum.inr (zF t a b)) 1 + Finsupp.single (Sum.inr (zT t a b)) 1) Q *
          (((ν (Sum.inr (zT t a b)) : ℤ) + 1) * ((ν (Sum.inr (zF t a b)) : ℤ) + 1)) := by
  unfold lapT
  simp only [LinearMap.sum_apply, MvPolynomial.coeff_sum, (show ∀ (f g : Module.End ℤ (PolyXZ H N0 N1)) (x : PolyXZ H N0 N1), (f * g) x = f (g x) from fun _ _ _ => rfl), coeff_pd_eq_coeff_add_single_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hne : (ν + Finsupp.single (Sum.inr (zF t a b)) 1 : XZ (Bool × H) N0 N1 →₀ ℕ) (Sum.inr (zT t a b)) =
      ν (Sum.inr (zT t a b)) := by
    simp [Finsupp.single_apply, zF, zT]
  rw [hne]
  ring

theorem symm_add_single (m : XV H N0 →₀ ℕ) (κ : ZV H N0 N1 →₀ ℕ) (v : ZV H N0 N1) :
    (Finsupp.sumFinsuppEquivProdFinsupp.symm (m, κ) : XZ (Bool × H) N0 N1 →₀ ℕ) +
        Finsupp.single (Sum.inr v) 1 =
      Finsupp.sumFinsuppEquivProdFinsupp.symm (m, κ + Finsupp.single v 1) := by
  ext x
  rcases x with x | x <;>
    simp [Finsupp.single_apply, Finsupp.sumFinsuppEquivProdFinsupp_symm_inl,
      Finsupp.sumFinsuppEquivProdFinsupp_symm_inr]

theorem symm_inr (m : XV H N0 →₀ ℕ) (κ : ZV H N0 N1 →₀ ℕ) (v : ZV H N0 N1) :
    (Finsupp.sumFinsuppEquivProdFinsupp.symm (m, κ) : XZ (Bool × H) N0 N1 →₀ ℕ) (Sum.inr v) = κ v := rfl

variable [Fintype H]

def wv (c κ : ZV H N0 N1 →₀ ℕ) : ℕ :=
  binomF c κ * ∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1, ((c - κ) ((true, t), a, b)).factorial

def wt (μ : XZ (Bool × H) N0 N1 →₀ ℕ) (m : XV H N0 →₀ ℕ) (κ : ZV H N0 N1 →₀ ℕ) (n : H → ℕ) : ℤ :=
  if xpart μ = m ∧ κ ≤ zpart μ ∧ Bal N0 N1 n (zpart μ - κ) then (wv (zpart μ) κ : ℤ) else 0

theorem acon_eq (P : PolyXZ H N0 N1) (m : XV H N0 →₀ ℕ) (κ : ZV H N0 N1 →₀ ℕ) (n : H → ℕ) :
    Acon P m κ n = ∑ μ ∈ P.support, MvPolynomial.coeff μ P * wt μ m κ n := by
  unfold Acon wt wv
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs <;> (try push_cast) <;> ring

theorem nest {M : Type} [CommMonoid M] (F : H → Fin N0 → Fin N1 → M) :
    ∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1, F t a b = ∏ x : H × Fin N0 × Fin N1, F x.1 x.2.1 x.2.2 := by
  simp only [Fintype.prod_prod_type]

theorem up_apply_false (κ : ZV H N0 N1 →₀ ℕ) (t : H) (a : Fin N0) (b : Fin N1) (t' : H) (a' : Fin N0)
    (b' : Fin N1) :
    up κ t a b ((false, t'), a', b') = κ ((false, t'), a', b') + if (t', a', b') = (t, a, b) then 1 else 0 := by
  simp only [up, zF, zT, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> simp_all

theorem up_apply_true (κ : ZV H N0 N1 →₀ ℕ) (t : H) (a : Fin N0) (b : Fin N1) (t' : H) (a' : Fin N0)
    (b' : Fin N1) :
    up κ t a b ((true, t'), a', b') = κ ((true, t'), a', b') + if (t', a', b') = (t, a, b) then 1 else 0 := by
  simp only [up, zF, zT, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> simp_all

theorem sum_ind (t t' : H) (a : Fin N0) (b : Fin N1) :
    (∑ a' : Fin N0, ∑ b' : Fin N1, if (t', a', b') = (t, a, b) then 1 else 0 : ℕ) = if t' = t then 1 else 0 := by
  by_cases ht : t' = t
  · subst ht
    rw [if_pos rfl, Finset.sum_eq_single a, Finset.sum_eq_single b]
    all_goals first
      | (simp; done)
      | (intro x _ hx; simp [hx]; done)
      | (intro x _ hx; exact Finset.sum_eq_zero fun y _ => by simp [hx])
  · rw [if_neg ht]
    exact Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => by simp [ht]

theorem bal_up (n n' : H → ℕ) (t : H) (hn : ∀ s, n s = n' s + if s = t then 1 else 0) (a : Fin N0)
    (b : Fin N1) (k : ZV H N0 N1 →₀ ℕ) : Bal N0 N1 n (up k t a b) ↔ Bal N0 N1 n' k := by
  unfold Bal
  simp only [up_apply_false, up_apply_true, Finset.sum_add_distrib, sum_ind, hn]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun s a' b' => Nat.add_right_cancel (h1 s a' b'), fun s => Nat.add_right_cancel (h2 s)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun s a' b' => by rw [h1 s a' b'], fun s => by rw [h2 s]⟩

private theorem finsupp_le_apply_of_le {c d : ZV H N0 N1 →₀ ℕ} (h : c ≤ d) (x : ZV H N0 N1) : c x ≤ d x := by
  first
    | exact h x
    | exact Finsupp.le_def.1 h x

theorem tsub_up {c κ : ZV H N0 N1 →₀ ℕ} {t : H} {a : Fin N0} {b : Fin N1} (hle : up κ t a b ≤ c) :
    c - κ = up (c - up κ t a b) t a b := by
  ext x
  have hx := finsupp_le_apply_of_le hle x
  simp only [up, Finsupp.tsub_apply, Finsupp.add_apply] at hx ⊢
  omega

theorem fact_up (k : ZV H N0 N1 →₀ ℕ) (t : H) (a : Fin N0) (b : Fin N1) :
    ∏ t' : H, ∏ a' : Fin N0, ∏ b' : Fin N1, ((up k t a b) ((true, t'), a', b')).factorial =
      (k (zT t a b) + 1) * ∏ t' : H, ∏ a' : Fin N0, ∏ b' : Fin N1, (k ((true, t'), a', b')).factorial := by
  simp only [nest]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun x : H × Fin N0 × Fin N1 => ((up k t a b) ((true, x.1), x.2.1, x.2.2)).factorial)
      (Finset.mem_univ (t, a, b)),
    ← Finset.mul_prod_erase Finset.univ
      (fun x : H × Fin N0 × Fin N1 => (k ((true, x.1), x.2.1, x.2.2)).factorial)
      (Finset.mem_univ (t, a, b))]
  have h1 : ∀ x ∈ (Finset.univ : Finset (H × Fin N0 × Fin N1)).erase (t, a, b),
      ((up k t a b) ((true, x.1), x.2.1, x.2.2)).factorial = (k ((true, x.1), x.2.1, x.2.2)).factorial := by
    intro x hx
    have hne : ¬ (x.1, x.2.1, x.2.2) = (t, a, b) := by simpa using hx
    rw [up_apply_true, if_neg hne, add_zero]
  rw [Finset.prod_congr rfl h1]
  try dsimp only
  rw [up_apply_true, if_pos rfl, Nat.factorial_succ]
  ring

private theorem up_zF (κ : ZV H N0 N1 →₀ ℕ) (t : H) (a : Fin N0) (b : Fin N1) :
    up κ t a b (zF t a b) = κ (zF t a b) + 1 := by
  rw [up_apply_false, if_pos rfl]

private theorem up_zT (κ : ZV H N0 N1 →₀ ℕ) (t : H) (a : Fin N0) (b : Fin N1) :
    up κ t a b (zT t a b) = κ (zT t a b) + 1 := by
  rw [up_apply_true, if_pos rfl]

private theorem succ_mul_succ_mul_mul_eq_of_mul_succ_eq (x y A A0 B B0 R d1 d2 : ℕ) (e1 : A * (x + 1) = A0 * d1) (e2 : B * (y + 1) = B0 * d2) :
    (y + 1) * (x + 1) * (A * (B * R)) = A0 * (B0 * R) * d1 * d2 := by
  calc (y + 1) * (x + 1) * (A * (B * R)) = (A * (x + 1)) * (B * (y + 1)) * R := by ring
    _ = (A0 * d1) * (B0 * d2) * R := by rw [e1, e2]
    _ = A0 * (B0 * R) * d1 * d2 := by ring

theorem binom_up {c κ : ZV H N0 N1 →₀ ℕ} {t : H} {a : Fin N0} {b : Fin N1} (hle : up κ t a b ≤ c) :
    (κ (zT t a b) + 1) * (κ (zF t a b) + 1) * binomF c (up κ t a b) =
      binomF c κ * ((c - κ) (zF t a b)) * ((c - κ) (zT t a b)) := by
  have hleF : κ (zF t a b) + 1 ≤ c (zF t a b) := by
    have h := finsupp_le_apply_of_le hle (zF t a b)
    rwa [up_zF] at h
  have hleT : κ (zT t a b) + 1 ≤ c (zT t a b) := by
    have h := finsupp_le_apply_of_le hle (zT t a b)
    rwa [up_zT] at h
  have hne : zT t a b ≠ zF t a b := by simp [zF, zT]
  have hF : zF t a b ∈ c.support := Finsupp.mem_support_iff.2 (by omega)
  have hT : zT t a b ∈ c.support.erase (zF t a b) :=
    Finset.mem_erase.2 ⟨hne, Finsupp.mem_support_iff.2 (by omega)⟩
  have hrest : ∀ v ∈ (c.support.erase (zF t a b)).erase (zT t a b),
      (c v).choose (up κ t a b v) = (c v).choose (κ v) := by
    intro v hv
    have hvT := Finset.ne_of_mem_erase hv
    have hvF := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hv)
    simp only [up, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hvF), if_neg (Ne.symm hvT),
      add_zero]
  unfold binomF
  rw [← Finset.mul_prod_erase c.support (fun v => (c v).choose (up κ t a b v)) hF,
    ← Finset.mul_prod_erase _ (fun v => (c v).choose (up κ t a b v)) hT,
    ← Finset.mul_prod_erase c.support (fun v => (c v).choose (κ v)) hF,
    ← Finset.mul_prod_erase _ (fun v => (c v).choose (κ v)) hT,
    Finset.prod_congr rfl hrest]
  try dsimp only
  rw [up_zF, up_zT, Finsupp.tsub_apply, Finsupp.tsub_apply]
  exact succ_mul_succ_mul_mul_eq_of_mul_succ_eq _ _ _ _ _ _ _ _ _ (Nat.choose_succ_right_eq _ _) (Nat.choose_succ_right_eq _ _)

private theorem alg_lemma_8 (p q B B0 P' F T : ℕ) (hB : p * q * B = B0 * F * T) (hFT : F = T) :
    p * q * (B * P') = B0 * (T * P') * T := by
  subst hFT
  calc p * q * (B * P') = (p * q * B) * P' := by ring
    _ = _ := by rw [hB]; ring

theorem wv_up {c κ : ZV H N0 N1 →₀ ℕ} {t : H} {a : Fin N0} {b : Fin N1} (hle : up κ t a b ≤ c)
    (hFG : (c - κ) (zF t a b) = (c - κ) (zT t a b)) :
    (κ (zT t a b) + 1) * (κ (zF t a b) + 1) * wv c (up κ t a b) = wv c κ * (c - κ) (zT t a b) := by
  have hB := binom_up hle
  have hP := fact_up (c - up κ t a b) t a b
  rw [← tsub_up hle] at hP
  have hv : (c - up κ t a b) (zT t a b) + 1 = (c - κ) (zT t a b) := by
    rw [tsub_up hle, up_zT]
  unfold wv
  rw [hP, hv]
  exact alg_lemma_8 _ _ _ _ _ _ _ hB hFG

private theorem up_le_of_le_of_lt_zF_of_lt_zT {c κ : ZV H N0 N1 →₀ ℕ} {t : H} {a : Fin N0} {b : Fin N1} (h : κ ≤ c)
    (hF : κ (zF t a b) < c (zF t a b)) (hT : κ (zT t a b) < c (zT t a b)) : up κ t a b ≤ c := by
  intro v
  have hv := finsupp_le_apply_of_le h v
  by_cases h1 : v = zF t a b
  · subst h1
    rw [up_zF]
    omega
  · by_cases h2 : v = zT t a b
    · subst h2
      rw [up_zT]
      omega
    · simp only [up, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]
      omega

theorem term_eq (μ : XZ (Bool × H) N0 N1 →₀ ℕ) (m : XV H N0 →₀ ℕ) (κ : ZV H N0 N1 →₀ ℕ) (n n' : H → ℕ)
    (t : H) (hn : ∀ s, n s = n' s + if s = t then 1 else 0) (a : Fin N0) (b : Fin N1) :
    ((κ (zT t a b) : ℤ) + 1) * ((κ (zF t a b) : ℤ) + 1) * wt μ m (up κ t a b) n' =
      if xpart μ = m ∧ κ ≤ zpart μ ∧ Bal N0 N1 n (zpart μ - κ) then
        (wv (zpart μ) κ : ℤ) * ((zpart μ - κ) (zT t a b) : ℤ) else 0 := by
  unfold wt
  by_cases hup : up κ t a b ≤ zpart μ
  · have hκ : κ ≤ zpart μ := le_trans (le_self_add.trans le_self_add) hup
    have hB : Bal N0 N1 n (zpart μ - κ) ↔ Bal N0 N1 n' (zpart μ - up κ t a b) := by
      rw [tsub_up hup]
      exact bal_up n n' t hn a b _
    have hiff : (xpart μ = m ∧ up κ t a b ≤ zpart μ ∧ Bal N0 N1 n' (zpart μ - up κ t a b)) ↔
        (xpart μ = m ∧ κ ≤ zpart μ ∧ Bal N0 N1 n (zpart μ - κ)) :=
      ⟨fun h => ⟨h.1, hκ, hB.2 h.2.2⟩, fun h => ⟨h.1, hup, hB.1 h.2.2⟩⟩
    by_cases h : xpart μ = m ∧ κ ≤ zpart μ ∧ Bal N0 N1 n (zpart μ - κ)
    · rw [if_pos (hiff.2 h), if_pos h]
      exact_mod_cast wv_up hup (h.2.2.1 t a b)
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, mul_zero]
  · have hn1 : ¬ (xpart μ = m ∧ up κ t a b ≤ zpart μ ∧ Bal N0 N1 n' (zpart μ - up κ t a b)) :=
      fun h' => hup h'.2.1
    rw [if_neg hn1, mul_zero]
    by_cases h : xpart μ = m ∧ κ ≤ zpart μ ∧ Bal N0 N1 n (zpart μ - κ)
    · rw [if_pos h]
      obtain ⟨-, hκ, hb⟩ := h
      have hFG : (zpart μ - κ) (zF t a b) = (zpart μ - κ) (zT t a b) := hb.1 t a b
      have e1 : (zpart μ - κ) (zF t a b) = zpart μ (zF t a b) - κ (zF t a b) := Finsupp.tsub_apply _ _ _
      have e2 : (zpart μ - κ) (zT t a b) = zpart μ (zT t a b) - κ (zT t a b) := Finsupp.tsub_apply _ _ _
      have h0 : (zpart μ - κ) (zT t a b) = 0 := by
        by_contra hne
        exact hup (up_le_of_le_of_lt_zF_of_lt_zT hκ (by omega) (by omega))
      rw [h0, Nat.cast_zero, mul_zero]
    · rw [if_neg h]

theorem mono_step (μ : XZ (Bool × H) N0 N1 →₀ ℕ) (m : XV H N0 →₀ ℕ) (κ : ZV H N0 N1 →₀ ℕ) (n n' : H → ℕ)
    (t : H) (hn : ∀ s, n s = n' s + if s = t then 1 else 0) :
    ((n' t : ℤ) + 1) * wt μ m κ n =
      ∑ a : Fin N0, ∑ b : Fin N1,
        ((κ (zT t a b) : ℤ) + 1) * ((κ (zF t a b) : ℤ) + 1) * wt μ m (up κ t a b) n' := by
  simp only [term_eq μ m κ n n' t hn]
  unfold wt
  by_cases h : xpart μ = m ∧ κ ≤ zpart μ ∧ Bal N0 N1 n (zpart μ - κ)
  · simp only [if_pos h]
    have hs := h.2.2.2 t
    rw [hn t, if_pos rfl] at hs
    have hs' : (∑ a : Fin N0, ∑ b : Fin N1, ((zpart μ - κ) (zT t a b) : ℤ)) = (n' t : ℤ) + 1 := by
      exact_mod_cast hs
    simp only [← Finset.mul_sum, hs']
    ring
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero]

theorem acon_step (P : PolyXZ H N0 N1) (m : XV H N0 →₀ ℕ) (κ : ZV H N0 N1 →₀ ℕ) (n n' : H → ℕ) (t : H)
    (hn : ∀ s, n s = n' s + if s = t then 1 else 0) :
    ((n' t : ℤ) + 1) * Acon P m κ n =
      ∑ a : Fin N0, ∑ b : Fin N1,
        ((κ (zT t a b) : ℤ) + 1) * ((κ (zF t a b) : ℤ) + 1) * Acon P m (up κ t a b) n' := by
  simp only [acon_eq, Finset.mul_sum]
  have hb : ∀ μ ∈ P.support,
      ((n' t : ℤ) + 1) * (MvPolynomial.coeff μ P * wt μ m κ n) =
        ∑ a : Fin N0, ∑ b : Fin N1, ((κ (zT t a b) : ℤ) + 1) * ((κ (zF t a b) : ℤ) + 1) *
          (MvPolynomial.coeff μ P * wt μ m (up κ t a b) n') := by
    intro μ _
    have := mono_step μ m κ n n' t hn
    calc ((n' t : ℤ) + 1) * (MvPolynomial.coeff μ P * wt μ m κ n)
        = MvPolynomial.coeff μ P * (((n' t : ℤ) + 1) * wt μ m κ n) := by ring
      _ = MvPolynomial.coeff μ P * ∑ a : Fin N0, ∑ b : Fin N1,
          ((κ (zT t a b) : ℤ) + 1) * ((κ (zF t a b) : ℤ) + 1) * wt μ m (up κ t a b) n' := by rw [this]
      _ = _ := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
  rw [Finset.sum_congr rfl hb, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

variable [DecidableEq H]

private theorem prod_factorial_eq_succ_mul_of_update (n n' : H → ℕ) (s : H) (hn : ∀ u, n u = n' u + if u = s then 1 else 0) :
    (∏ u : H, ((n u).factorial : ℤ)) = ((n' s : ℤ) + 1) * ∏ u : H, ((n' u).factorial : ℤ) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun u => ((n u).factorial : ℤ)) (Finset.mem_univ s),
    ← Finset.mul_prod_erase Finset.univ (fun u => ((n' u).factorial : ℤ)) (Finset.mem_univ s)]
  have h1 : ∀ u ∈ (Finset.univ : Finset H).erase s, ((n u).factorial : ℤ) = ((n' u).factorial : ℤ) := by
    intro u hu
    rw [hn u, if_neg (Finset.ne_of_mem_erase hu), add_zero]
  rw [Finset.prod_congr rfl h1]
  try dsimp only
  rw [hn s, if_pos rfl, Nat.factorial_succ]
  push_cast
  ring

private theorem bal_zero_iff (k : ZV H N0 N1 →₀ ℕ) : Bal N0 N1 (fun _ => 0) k ↔ k = 0 := by
  unfold Bal
  constructor
  · rintro ⟨h1, h2⟩
    have hT : ∀ t a b, k ((true, t), a, b) = 0 := by
      intro t a b
      have h : ∑ a : Fin N0, ∑ b : Fin N1, k ((true, t), a, b) = 0 := h2 t
      rw [Finset.sum_eq_zero_iff] at h
      have h' := h a (Finset.mem_univ _)
      rw [Finset.sum_eq_zero_iff] at h'
      exact h' b (Finset.mem_univ _)
    ext ⟨⟨bb, t⟩, a, b⟩
    cases bb
    · simp [h1 t a b, hT t a b]
    · simp [hT t a b]
  · rintro rfl
    exact ⟨fun _ _ _ => rfl, fun _ => by simp⟩

theorem bridge_list (L : List H) (P : PolyXZ H N0 N1) (m : XV H N0 →₀ ℕ) (κ : ZV H N0 N1 →₀ ℕ) :
    (∏ t : H, ((L.count t).factorial : ℤ)) * Acon P m κ (fun t => L.count t) =
      MvPolynomial.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (m, κ)) ((L.map (lapT N0 N1)).prod P) := by
  induction L generalizing κ with
  | nil =>
    simp only [List.count_nil, Nat.factorial_zero, Nat.cast_one, Finset.prod_const_one, one_mul,
      List.map_nil, List.prod_nil, (show ∀ (x : PolyXZ H N0 N1), (1 : Module.End ℤ (PolyXZ H N0 N1)) x = x from fun _ => rfl)]
    unfold Acon
    have key : ∀ μ : XZ (Bool × H) N0 N1 →₀ ℕ,
        (xpart μ = m ∧ κ ≤ zpart μ ∧ Bal N0 N1 (fun _ => 0) (zpart μ - κ)) ↔
          μ = Finsupp.sumFinsuppEquivProdFinsupp.symm (m, κ) := by
      intro μ
      rw [bal_zero_iff, tsub_eq_zero_iff_le]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have hz : zpart μ = κ := le_antisymm h3 h2
        rw [← h1, ← hz]
        simp [xpart, zpart]
      · rintro rfl
        simp [xpart, zpart]
    rw [Finset.sum_eq_single (Finsupp.sumFinsuppEquivProdFinsupp.symm (m, κ))]
    · rw [if_pos ((key _).2 rfl)]
      simp [zpart, binomF]
    · intro μ _ hne
      rw [if_neg (fun h => hne ((key μ).1 h))]
    · intro hν
      rw [if_pos ((key _).2 rfl)]
      have h0 : MvPolynomial.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (m, κ)) P = 0 := by
        by_contra h
        exact hν (MvPolynomial.mem_support_iff.2 h)
      rw [h0, zero_mul, zero_mul]
  | cons s L ih =>
    have hn : ∀ u, (s :: L).count u = L.count u + if u = s then 1 else 0 := by
      intro u
      by_cases h : u = s
      · subst h
        simp [List.count_cons]
      · simp [List.count_cons, h, Ne.symm h]
    rw [prod_factorial_eq_succ_mul_of_update (fun u => (s :: L).count u) (fun u => L.count u) s hn]
    rw [List.map_cons, List.prod_cons, (show ∀ (f g : Module.End ℤ (PolyXZ H N0 N1)) (x : PolyXZ H N0 N1), (f * g) x = f (g x) from fun _ _ _ => rfl), coeff_lapT]
    simp only [symm_add_single, symm_inr, ← ih]
    rw [mul_right_comm, acon_step P m κ (fun u => (s :: L).count u) (fun u => L.count u) s
      (fun u => by rw [hn u]; split_ifs <;> rfl),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

private theorem prod_map_flatMap_replicate (n : H → ℕ) (l : List H) :
    ((l.flatMap fun t => List.replicate (n t) t).map (lapT N0 N1)).prod =
      (l.map fun t => lapT N0 N1 t ^ n t).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem lapAll_eq_list (n : H → ℕ) :
    lapAll (H := H) N0 N1 n =
      (((Finset.univ : Finset H).toList.flatMap fun t => List.replicate (n t) t).map (lapT N0 N1)).prod := by
  unfold lapAll
  rw [prod_map_flatMap_replicate]

private theorem count_flatMap_replicate (n : H → ℕ) (s : H) (l : List H) :
    (l.flatMap fun t => List.replicate (n t) t).count s = (l.map fun t => if t = s then n t else 0).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases h : x = s
    · subst h
      simp [ih]
    · simp [ih, h, Ne.symm h, List.count_replicate, List.count_append]

theorem count_list (n : H → ℕ) (s : H) :
    ((Finset.univ : Finset H).toList.flatMap fun t => List.replicate (n t) t).count s = n s := by
  rw [count_flatMap_replicate]
  first
    | (rw [Finset.sum_map_toList]; simp; done)
    | (simp [Finset.sum_map_toList]; done)
    | (simp [Finset.sum_toList]; done)
    | (rw [← Finset.sum_toList]; simp; done)

end Br

theorem pBridge : PBridge := by
  unfold PBridge
  intro H _ _ N0 N1 P m κ2 n
  have h := Br.bridge_list (H := H) ((Finset.univ : Finset H).toList.flatMap fun t => List.replicate (n t) t)
    P m κ2
  simp only [Br.count_list] at h
  rw [Br.lapAll_eq_list]
  exact h

end PI.EntAtD.W
