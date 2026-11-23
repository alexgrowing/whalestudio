import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

def blockIndexWeight {B n : ℕ} (b : Fin B) : Fin B × Fin n → ℕ := fun p => if p.1 = b then 1 else 0

theorem weight_lh0BlockWt_apply {B n : ℕ} (b : Fin B) (s : Fin B × Fin n →₀ ℕ) :
    Finsupp.weight (blockIndexWeight (n := n) b) s = ∑ j : Fin n, s (b, j) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [blockIndexWeight, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp

theorem isMultiHomogeneous_iff_forall_weighted_lh0BlockWt {R : Type*} [CommSemiring R] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) R) :
    IsMultiHomogeneous a f ↔ ∀ b, IsWeightedHomogeneous (blockIndexWeight b) f (a b) := by
  simp only [IsMultiHomogeneous, IsWeightedHomogeneous, weight_lh0BlockWt_apply, mem_support_iff]
  constructor
  · intro h b d hd
    exact h d hd b
  · intro h s hs b
    exact h b hs

theorem eval_mul_of_isMultiHomogeneous {B n : ℕ} {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (c : ℂ) (z : Fin B × Fin n → ℂ) :
    eval (fun p => c * z p) g = c ^ (∑ b, a b) * eval z g := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : ∑ p, s p = ∑ b, a b := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ => hg s hs b
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

private lemma sum_primitiveRoot_pow_mul_inv_pow_eq_ite {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ}
    (ha : a < N) (hb : b < N) :
    ∑ j : Fin N, (ζ ^ a * ζ⁻¹ ^ b) ^ (j : ℕ) = if a = b then (N : ℂ) else 0 := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le a) ha
  have hz : ζ ≠ 0 := hζ.ne_zero hN.ne'
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ a * ζ⁻¹ ^ b) ^ j) N]
  split_ifs with hab
  · subst hab
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    simp
  · have hω1 : ζ ^ a * ζ⁻¹ ^ b ≠ 1 := by
      intro h
      apply hab
      apply hζ.pow_inj ha hb
      rwa [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hz)] at h
    have hωN : (ζ ^ a * ζ⁻¹ ^ b) ^ N = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a, Nat.mul_comm b, pow_mul, pow_mul, inv_pow,
        hζ.pow_eq_one]
      simp
    rw [geom_sum_eq hω1, hωN]
    simp

theorem exists_torus_coeff_le {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∃ z : ι → ℂ, (∀ i, ‖z i‖ = 1) ∧ ‖coeff s g‖ ≤ ‖eval z g‖ := by
  classical
  by_cases hs : s ∈ g.support
  swap
  · refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    rw [show coeff s g = 0 by simpa using hs, norm_zero]
    exact norm_nonneg _
  obtain ⟨N, hN⟩ : ∃ N, N = g.totalDegree + 1 := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by omega
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hN0⟩
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hN0
  have hlt : ∀ d ∈ g.support, ∀ i, d i < N := by
    intro d hd i
    have h1 : d i ≤ d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    have h2 := le_totalDegree hd
    omega
  let z : (ι → Fin N) → ι → ℂ := fun k i => ζ ^ (k i : ℕ)
  let c : (ι → Fin N) → ℂ := fun k => ∏ i, ζ⁻¹ ^ ((k i : ℕ) * s i)
  have key : ∑ k, eval (z k) g * c k = (N : ℂ) ^ Fintype.card ι * coeff s g := by
    calc ∑ k, eval (z k) g * c k
        = ∑ d ∈ g.support, coeff d g * ∏ i, ∑ j : Fin N, (ζ ^ d i * ζ⁻¹ ^ s i) ^ (j : ℕ) := by
          simp only [eval_eq', Finset.sum_mul, z, c]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm (d i), Nat.mul_comm (s i)]
      _ = ∑ d ∈ g.support, coeff d g * (if d = s then (N : ℂ) ^ Fintype.card ι else 0) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          congr 1
          simp_rw [sum_primitiveRoot_pow_mul_inv_pow_eq_ite hζ (hlt d hd _) (hlt s hs _)]
          split_ifs with hds
          · subst hds
            simp
          · obtain ⟨i, hi⟩ : ∃ i, d i ≠ s i := by
              by_contra h
              push_neg at h
              exact hds (Finsupp.ext h)
            exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
      _ = (N : ℂ) ^ Fintype.card ι * coeff s g := by
          rw [Finset.sum_eq_single s (fun d _ hd => by simp [hd]) (fun h => absurd hs h)]
          simp [mul_comm]
  by_contra hcon
  push_neg at hcon
  have hlt2 : ∀ k, ‖eval (z k) g * c k‖ < ‖coeff s g‖ := by
    intro k
    have hc : ‖c k‖ = 1 := by simp [c, norm_prod, norm_pow, norm_inv, hζn]
    rw [norm_mul, hc, mul_one]
    exact hcon (z k) (fun i => by simp [z, norm_pow, hζn])
  have hsum := norm_sum_le (Finset.univ : Finset (ι → Fin N)) (fun k => eval (z k) g * c k)
  have hsum2 : ∑ k, ‖eval (z k) g * c k‖ < ∑ _k : ι → Fin N, ‖coeff s g‖ :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hlt2 k)
  rw [key, norm_mul, norm_pow, Complex.norm_natCast] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul] at hsum2
  push_cast at hsum2
  linarith

end ReciprocityTheory.MultiplicativeHeights
