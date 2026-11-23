import Formalism.GradedWeylDivisibility.StatementA

open Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma antitone_prod_pow_dominance (t : ℕ → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht : Antitone t) (μ lam : ℕ → ℕ) :
    ∀ N : ℕ, (∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a) →
      ∀ c : ℝ, 0 ≤ c → (∀ a < N, c ≤ t a) →
      (∏ a ∈ range N, t a ^ μ a) * c ^ (∑ a ∈ range N, lam a - ∑ a ∈ range N, μ a) ≤
        ∏ a ∈ range N, t a ^ lam a := by
  intro N
  induction N with
  | zero => intro _ c _ _; simp
  | succ N ih =>
    intro hS c hc hct
    have hSN : ∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a := fun k hk => hS k (by omega)
    have hN := hS N (by omega)
    have hN1 := hS (N + 1) le_rfl
    simp only [Finset.sum_range_succ, Finset.prod_range_succ] at hN1 ⊢
    set Pm := ∏ a ∈ range N, t a ^ μ a with hPm
    set Pl := ∏ a ∈ range N, t a ^ lam a with hPl
    set M := ∑ a ∈ range N, μ a with hM
    set L := ∑ a ∈ range N, lam a with hL
    have htN : 0 ≤ t N := ht0 N
    have hPm0 : 0 ≤ Pm := Finset.prod_nonneg fun a _ => pow_nonneg (ht0 a) _
    have hPl0 : 0 ≤ Pl := Finset.prod_nonneg fun a _ => pow_nonneg (ht0 a) _
    have hcN : c ≤ t N := hct N (by omega)
    rcases le_total (μ N) (lam N) with h | h
    · have e : L + lam N - (M + μ N) = (L - M) + (lam N - μ N) := by omega
      rw [e, pow_add]
      have ih' := ih hSN c hc (fun a ha => hct a (by omega))
      have h2 : t N ^ μ N * c ^ (lam N - μ N) ≤ t N ^ lam N := by
        calc t N ^ μ N * c ^ (lam N - μ N) ≤ t N ^ μ N * t N ^ (lam N - μ N) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hcN _) (pow_nonneg htN _)
          _ = t N ^ lam N := by rw [← pow_add, Nat.add_sub_cancel' h]
      calc Pm * t N ^ μ N * (c ^ (L - M) * c ^ (lam N - μ N))
          = (Pm * c ^ (L - M)) * (t N ^ μ N * c ^ (lam N - μ N)) := by ring
        _ ≤ Pl * t N ^ lam N :=
          mul_le_mul ih' h2 (mul_nonneg (pow_nonneg htN _) (pow_nonneg hc _)) hPl0
    · have ih' := ih hSN (t N) htN (fun a ha => ht (show a ≤ N by omega))
      have e2 : t N ^ μ N * t N ^ (L + lam N - (M + μ N)) = t N ^ (L - M) * t N ^ lam N := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      calc Pm * t N ^ μ N * c ^ (L + lam N - (M + μ N))
          ≤ Pm * t N ^ μ N * t N ^ (L + lam N - (M + μ N)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hcN _)
              (mul_nonneg hPm0 (pow_nonneg htN _))
        _ = Pm * t N ^ (L - M) * t N ^ lam N := by rw [mul_assoc, e2, ← mul_assoc]
        _ ≤ Pl * t N ^ lam N := mul_le_mul_of_nonneg_right ih' (pow_nonneg htN _)

lemma ldiag_domPow_nat (t : ℕ → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht : Antitone t) (μ lam : ℕ → ℕ) (N : ℕ)
    (hS : ∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a)
    (hT : ∑ a ∈ range N, μ a = ∑ a ∈ range N, lam a) :
    ∏ a ∈ range N, t a ^ μ a ≤ ∏ a ∈ range N, t a ^ lam a := by
  have h := antitone_prod_pow_dominance t ht0 ht μ lam N hS 0 le_rfl (fun a _ => ht0 a)
  rwa [hT, Nat.sub_self, pow_zero, mul_one] at h

def ldiagExt {α : Type*} [Zero α] {r : ℕ} (f : Fin r → α) (a : ℕ) : α :=
  if h : a < r then f ⟨a, h⟩ else 0

lemma ldiag_ext_fin {α : Type*} [Zero α] {r : ℕ} (f : Fin r → α) (a : Fin r) : ldiagExt f a = f a := by
  rw [ldiagExt, dif_pos a.isLt]

lemma ldiag_sum_filter_lt_eq_range {r : ℕ} (f : Fin r → ℕ) (k : ℕ) (hk : k ≤ r) :
    ∑ a : Fin r with a.val < k, f a = ∑ a ∈ range k, ldiagExt f a := by
  rw [Finset.sum_filter]
  have h1 : ∀ a : Fin r, (if a.val < k then f a else 0) =
      (fun i : ℕ => if i < k then ldiagExt f i else 0) a.val := fun a => by
    simp only [ldiag_ext_fin]
  rw [Finset.sum_congr rfl (fun a _ => h1 a),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < k then ldiagExt f i else 0) r, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by omega, h⟩

lemma ldiag_sum_univ_eq_range {r : ℕ} (f : Fin r → ℕ) :
    ∑ a : Fin r, f a = ∑ a ∈ range r, ldiagExt f a := by
  have h := ldiag_sum_filter_lt_eq_range f r le_rfl
  simpa using h

lemma ldiag_prod_univ_eq_range {r : ℕ} (t : Fin r → ℝ) (μ : Fin r → ℕ) :
    ∏ a : Fin r, t a ^ μ a = ∏ a ∈ range r, ldiagExt t a ^ ldiagExt μ a := by
  rw [← Fin.prod_univ_eq_prod_range (fun i : ℕ => ldiagExt t i ^ ldiagExt μ i) r]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [ldiag_ext_fin]

theorem dominancePowerProduct_holds : DomPow := by
  intro r t μ lam ht0 ht hS hT
  rw [ldiag_prod_univ_eq_range, ldiag_prod_univ_eq_range]
  have hext0 : ∀ a, 0 ≤ ldiagExt t a := fun a => by
    unfold ldiagExt; split_ifs
    · exact ht0 _
    · exact le_rfl
  refine ldiag_domPow_nat (ldiagExt t) hext0 ?_ (ldiagExt μ) (ldiagExt lam) r ?_ ?_
  · intro a b hab
    by_cases hb : b < r
    · have ha : a < r := lt_of_le_of_lt hab hb
      simp only [ldiagExt, dif_pos ha, dif_pos hb]
      exact ht (show (⟨a, ha⟩ : Fin r) ≤ ⟨b, hb⟩ from hab)
    · simp only [ldiagExt, dif_neg hb]
      exact hext0 a
  · intro k hk
    rw [← ldiag_sum_filter_lt_eq_range μ k hk, ← ldiag_sum_filter_lt_eq_range lam k hk]
    exact hS k
  · rw [← ldiag_sum_univ_eq_range, ← ldiag_sum_univ_eq_range]
    exact hT

end Formalism.GradedWeylDivisibility
