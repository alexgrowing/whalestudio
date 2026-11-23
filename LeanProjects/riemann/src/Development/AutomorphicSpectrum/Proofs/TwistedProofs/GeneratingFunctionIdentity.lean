import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertGenFun

theorem hasSum_counts (q N c : ℕ) (X : ℂ) (h : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j)
      (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2)) := by
  set y : ℂ := (q : ℂ) ^ (N + 1) * X with hy
  set F : ℕ → ℂ := fun j => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j with hF
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have hev : HasSum (fun m : ℕ => F (2 * m)) (c * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m)) = fun m => (c : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2), hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hodd : HasSum (fun m : ℕ => F (2 * m + 1)) (c * q * X * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m + 1)) = fun m => (c * q * X : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [show (2 * m + 1) / 2 = m by omega, hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hne : (1 : ℂ) - y ^ 2 ≠ 0 := by
    intro h0
    have : ‖y ^ 2‖ = 1 := by
      rw [show y ^ 2 = 1 by linear_combination -h0]
      simp
    linarith
  have hval : (c : ℂ) * (1 + q * X) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * X * (1 - y ^ 2)⁻¹ := by
    field_simp
  rw [hval]
  exact HasSum.even_add_odd hev hodd

theorem hasSum_of_counts {ι : Type} (g : ι → ℕ) (A : ℕ → ℕ) (hA : ∀ j, A j ≠ 0)
    (hc : ∀ j, Nat.card {i // g i ≤ j} = A j) (X s : ℂ)
    (hT : HasSum (fun j : ℕ => (A j : ℂ) * X ^ j) s) :
    HasSum (fun i => X ^ g i) ((1 - X) * s) := by
  have hfinle : ∀ j, Finite {i // g i ≤ j} := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hc j]; exact hA j)
  have hfin : ∀ j, Finite {i // g i = j} := fun j =>
    Finite.of_injective (fun c : {i // g i = j} => (⟨c.1, c.2.le⟩ : {i // g i ≤ j}))
      (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have hcard : ∀ j, Nat.card {i // g i = j} + (if j = 0 then 0 else A (j - 1)) = A j := by
    intro j
    rcases j with _ | k
    · simp only [if_true, add_zero, ← hc 0]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by omega))
    · have : ∀ i, g i ≤ k + 1 ↔ g i ≤ k ∨ g i = k + 1 := fun i => by omega
      have e := (Equiv.subtypeEquivRight this).trans
        (subtypeOrEquiv (fun i => g i ≤ k) (fun i => g i = k + 1)
          (Pi.disjoint_iff.2 fun i => Prop.disjoint_iff.2 (by omega)))
      rw [← hc (k + 1), Nat.card_congr e, Nat.card_sum, if_neg (Nat.succ_ne_zero k),
        Nat.add_sub_cancel, ← hc k, add_comm]
  have hfib : ∀ (j : ℕ) {M : Type} [AddCommMonoid M] [TopologicalSpace M] (F : ℕ → M),
      HasSum (fun c : {i // g i = j} => F (g c)) (Nat.card {i // g i = j} • F j) := by
    intro j M _ _ F
    have := hfin j
    have : Fintype {i // g i = j} := Fintype.ofFinite _
    convert hasSum_fintype (fun c : {i // g i = j} => F (g c)) using 1
    rw [Finset.sum_congr rfl (fun c _ => by rw [c.2]), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hle : ∀ j, Nat.card {i // g i = j} ≤ A j := fun j => by
    have := hcard j
    omega
  have hnorm : Summable (fun j : ℕ => (A j : ℝ) * ‖X‖ ^ j) := by
    have := hT.summable.norm
    simpa [norm_mul, norm_pow] using this
  have hsum : Summable (fun i => X ^ g i) := by
    apply Summable.of_norm
    rw [← (Equiv.sigmaFiberEquiv g).summable_iff]
    show Summable fun p : (Σ j : ℕ, {i // g i = j}) => ‖X ^ g (p.2 : ι)‖
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun j => (hfib j (fun n => ‖X ^ n‖)).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => norm_nonneg _) (fun j => ?_) hnorm
    have h1 := (hfib j (fun n => ‖X ^ n‖)).tsum_eq
    rw [h1, nsmul_eq_mul, norm_pow]
    gcongr
    exact_mod_cast hle j
  obtain ⟨t, ht⟩ := hsum
  have hsig := ((Equiv.sigmaFiberEquiv g).hasSum_iff.2 ht).sigma
    (fun j => hfib j (fun n => X ^ n))
  have hshift : HasSum (fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) (s * X) := by
    have h0 : HasSum (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1))
        (s * X) := by
      have hfun : (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1)) =
          fun n => (A n : ℂ) * X ^ n * X := by
        funext n
        rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, pow_succ]
        ring
      rw [hfun]
      exact hT.mul_right X
    have h1 := (hasSum_nat_add_iff
      (f := fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) 1).1 h0
    simp only [Finset.sum_range_one, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero] at h1
    exact h1
  have hdiff := hT.sub hshift
  have heq : (fun j : ℕ => (A j : ℂ) * X ^ j - ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) =
      fun j => Nat.card {i // g i = j} • X ^ j := by
    funext j
    rw [nsmul_eq_mul, ← hcard j]
    push_cast
    ring
  rw [heq] at hdiff
  have := hsig.unique hdiff
  rw [this] at ht
  rwa [show (1 - X) * s = s - s * X by ring]

theorem genFun : GenFun := by
  intro ι f l c q N X hc hq hf hcount hX
  have hA : ∀ j, c * q ^ (2 * N * (j / 2) + j) ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hcg : ∀ j, Nat.card {i // f i - l ≤ j} = c * q ^ (2 * N * (j / 2) + j) := by
    intro j
    rw [← hcount j]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by have := hf i; omega))
  have h := hasSum_of_counts (fun i => f i - l) (fun j => c * q ^ (2 * N * (j / 2) + j)) hA hcg X _
    (hasSum_counts q N c X hX)
  have key : (fun i => X ^ f i) = fun i => X ^ l * X ^ (f i - l) := by
    funext i
    rw [← pow_add]
    congr 1
    have := hf i
    omega
  rw [key, show (c : ℂ) * X ^ l * jFac q N X =
    X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
  exact h.mul_left _

end GlobalTheory.CompanionTheory.InertGenFun
