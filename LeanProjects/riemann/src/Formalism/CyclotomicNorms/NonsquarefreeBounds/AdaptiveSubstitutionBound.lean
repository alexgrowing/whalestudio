import Formalism.CyclotomicNorms.DiscardKernel
import Formalism.CyclotomicNorms.NonsquarefreeBounds.SubstitutionBound

open Finset

noncomputable section

namespace Formalism.CyclotomicNorms

namespace AdaptiveSubstitution

def step (ℓ A : ℕ) (B : List ℕ → ℕ) (L : List ℕ) : ℕ :=
  B L + A * (L.map (ℓ ^ ·)).sum + L.sum + 1

def pre (ℓ A : ℕ) (B : List ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre ℓ A B n ++ [step ℓ A B (pre ℓ A B n)]

theorem pre_eq (ℓ A : ℕ) (B : List ℕ → ℕ) (n : ℕ) :
    pre ℓ A B n = List.ofFn (fun i : Fin n => step ℓ A B (pre ℓ A B i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    rfl

theorem mem_pre (ℓ A : ℕ) (B : List ℕ → ℕ) {i n : ℕ} (h : i < n) :
    step ℓ A B (pre ℓ A B i) ∈ pre ℓ A B n := by
  rw [pre_eq ℓ A B n, List.mem_ofFn]
  exact ⟨⟨i, h⟩, rfl⟩

theorem exists_exps_adaptive (ℓ : ℕ) {r s : ℕ} (hℓ : 2 ≤ ℓ) (α : Fin s → Fin r →₀ ℕ)
    (B : List ℕ → ℕ) :
    ∃ e : Fin r → ℕ, StrictMono e ∧
      (∀ j : Fin r, B (List.ofFn fun i : Fin (j : ℕ) => e (Fin.castLE (Nat.le_of_lt j.isLt) i)) ≤ e j) ∧
      ∀ t j, ∑ i ∈ univ.filter (· < j), α t i * ℓ ^ e i < ℓ ^ e j := by
  set A : ℕ := ∑ t, ∑ i, α t i with hA
  have hαA : ∀ t, ∑ i, α t i ≤ A := fun t =>
    Finset.single_le_sum (f := fun t' => ∑ i', α t' i') (fun _ _ => Nat.zero_le _) (mem_univ t)
  have hℓpos : 0 < ℓ := by omega
  refine ⟨fun j => step ℓ A B (pre ℓ A B j), ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hm := mem_pre ℓ A B hab'
    have hle := List.le_sum_of_mem hm
    simp only [step] at hle ⊢
    omega
  · intro j
    have : (List.ofFn fun i : Fin (j : ℕ) =>
        step ℓ A B (pre ℓ A B (Fin.castLE (Nat.le_of_lt j.isLt) i : ℕ))) = pre ℓ A B j := by
      rw [pre_eq ℓ A B j]
      rfl
    simp only
    rw [this]
    simp only [step]
    omega
  · intro t j
    set S := ((pre ℓ A B j).map (ℓ ^ ·)).sum with hS
    have hterm : ∀ i ∈ univ.filter (· < j),
        α t i * ℓ ^ step ℓ A B (pre ℓ A B i) ≤ α t i * S := by
      intro i hi
      have hij : (i : ℕ) < j := by simpa using hi
      apply Nat.mul_le_mul_left
      exact List.le_sum_of_mem (List.mem_map_of_mem (mem_pre ℓ A B hij))
    have h1 : ∑ i ∈ univ.filter (· < j), α t i * ℓ ^ step ℓ A B (pre ℓ A B i) ≤ A * S := by
      calc ∑ i ∈ univ.filter (· < j), α t i * ℓ ^ step ℓ A B (pre ℓ A B i)
          ≤ ∑ i ∈ univ.filter (· < j), α t i * S := Finset.sum_le_sum hterm
        _ ≤ ∑ i, α t i * S :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
        _ = (∑ i, α t i) * S := by rw [Finset.sum_mul]
        _ ≤ A * S := Nat.mul_le_mul_right _ (hαA t)
    have h2 : A * S < step ℓ A B (pre ℓ A B j) := by
      simp only [step, ← hS]
      omega
    have h3 : step ℓ A B (pre ℓ A B j) < ℓ ^ step ℓ A B (pre ℓ A B j) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hℓ _)
    simp only
    omega

end AdaptiveSubstitution

open SubstitutionExponents AdaptiveSubstitution in
theorem adaptive_substitution_bound : SubstitutionAdaptive := by
  intro k _ ℓ r s F B hℓ hF
  classical
  have hne : ∀ t, {d | MvPowerSeries.coeff d (F t) ≠ 0}.Nonempty := fun t =>
    (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero _).1 (hF t)
  let α : Fin s → (Fin r →₀ ℕ) := fun t => (revLex_wf (r := r)).min _ (hne t)
  obtain ⟨e, he1, he2, he3⟩ := exists_exps_adaptive ℓ hℓ α B
  refine ⟨e, he1, he2, fun t h0 => ?_⟩
  have hn : ∀ j, ℓ ^ e j ≠ 0 := fun j => pow_ne_zero _ (by omega)
  have hc := congrArg (PowerSeries.coeff (weight (fun j => ℓ ^ e j) (α t))) h0
  rw [coeff_subst_weight (fun j => ℓ ^ e j) hn, map_zero,
    finsum_eq_single _ (α t)] at hc
  · rw [if_pos rfl] at hc
    exact (revLex_wf (r := r)).min_mem _ (hne t) hc
  · intro d hd
    by_cases hw : weight (fun j => ℓ ^ e j) d = weight (fun j => ℓ ^ e j) (α t)
    · rw [if_pos hw]
      by_contra hcd
      exact hd (unique_of_min _ (α t) (he3 t) d
        ((revLex_wf (r := r)).not_lt_min _ (show d ∈ {d | MvPowerSeries.coeff d (F t) ≠ 0} from hcd)) hw)
    · rw [if_neg hw]

end Formalism.CyclotomicNorms
