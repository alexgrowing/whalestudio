import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob

open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem orth {K : Type*} [Field K] {M : ℕ} (hM : 0 < M) {ξ : K} (hξ : IsPrimitiveRoot ξ M) {x y : ℕ}
    (hx : x < M) (hy : y < M) :
    ∑ k ∈ Finset.range M, ξ ^ (M - (k * x) % M) * (ξ ^ k) ^ y = if y = x then (M : K) else 0 := by
  have hξ0 : ξ ≠ 0 := hξ.ne_zero hM.ne'
  have hterm : ∀ k, ξ ^ (M - (k * x) % M) * (ξ ^ k) ^ y = (ξ ^ y / ξ ^ x) ^ k := by
    intro k
    have h1 : ξ ^ (M - (k * x) % M) * ξ ^ (k * x) = 1 := by
      have hlt : (k * x) % M ≤ M := (Nat.mod_lt _ hM).le
      have e1 : ξ ^ (k * x) = ξ ^ ((k * x) % M) := by
        conv_lhs => rw [← Nat.mod_add_div (k * x) M]
        rw [pow_add, pow_mul, hξ.pow_eq_one, one_pow, mul_one]
      rw [e1, ← pow_add, Nat.sub_add_cancel hlt, hξ.pow_eq_one]
    rw [div_pow, eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hξ0))]
    simp only [← pow_mul]
    rw [mul_right_comm, mul_comm x k, h1, one_mul, mul_comm y k]
  simp_rw [hterm]
  split_ifs with hxy
  · subst hxy
    simp [div_self (pow_ne_zero _ hξ0)]
  · have hu1 : ξ ^ y / ξ ^ x ≠ 1 := by
      intro h
      apply hxy
      rw [div_eq_one_iff_eq (pow_ne_zero _ hξ0)] at h
      exact hξ.pow_inj hy hx h
    have huM : (ξ ^ y / ξ ^ x) ^ M = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm y, mul_comm x, pow_mul, pow_mul,
        hξ.pow_eq_one, one_pow, one_pow, div_one]
    rw [geom_sum_eq hu1, huM, sub_self, zero_div]

private theorem exact_sum {K : Type*} [Field K] {M : ℕ} (hM : 0 < M) {ξ : K} (hξ : IsPrimitiveRoot ξ M)
    (N : (ZMod M → K) →ₗ[K] K) (l : ℕ) (h : ℕ → K) :
    ∑ x ∈ (Finset.range M).filter (fun x => ¬ l ∣ x),
        h x * ∑ k ∈ Finset.range M, ξ ^ (M - (k * x) % M) * N (fun y => (ξ ^ k) ^ y.val) =
      (M : K) * N (fun y => if l ∣ y.val then 0 else h y.val) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have key : ∀ x ∈ (Finset.range M).filter (fun x => ¬ l ∣ x),
      ∑ k ∈ Finset.range M, ξ ^ (M - (k * x) % M) * N (fun y : ZMod M => (ξ ^ k) ^ y.val) =
      N (fun y : ZMod M => if y.val = x then (M : K) else 0) := by
    intro x hx
    have hxM : x < M := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    have hfun : (fun y : ZMod M => if y.val = x then (M : K) else 0) =
        ∑ k ∈ Finset.range M, ξ ^ (M - (k * x) % M) • (fun y : ZMod M => (ξ ^ k) ^ y.val) := by
      funext y
      rw [Finset.sum_apply, ← orth hM hξ hxM (ZMod.val_lt y)]
      simp [smul_eq_mul]
    rw [hfun, map_sum]
    simp [map_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun x hx => by rw [key x hx])]
  have hφ : (M : K) • (fun y : ZMod M => if l ∣ y.val then 0 else h y.val) =
      ∑ x ∈ (Finset.range M).filter (fun x => ¬ l ∣ x),
        h x • (fun y : ZMod M => if y.val = x then (M : K) else 0) := by
    funext y
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    have hy := ZMod.val_lt y
    by_cases hly : l ∣ y.val
    · simp [hly]
    · simp [hly, hy, mul_comm]
  rw [← smul_eq_mul (M : K), ← map_smul, hφ, map_sum]
  simp [map_smul, smul_eq_mul]

theorem UpperTheory.restriction_to_units_congr_of_measure :
    ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (N : (ZMod (l ^ r) → Qbar l) →ₗ[Qbar l] Qbar l) (L : PowerSeries (Qbar l)),
      (∀ z : Qbar l, z ^ (l ^ r) = 1 → Cg (2 * r) (tval L (l ^ (3 * r)) z) (N (fun x => z ^ x.val))) →
      ∀ (ξ : Qbar l), IsPrimitiveRoot ξ (l ^ r) → ∀ (h : ℕ → Qbar l), (∀ x, ‖h x‖ ≤ 1) →
        Cg (2 * r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), h x * mass L r ξ x)
          ((l : Qbar l) ^ r * N (fun y => if l ∣ y.val then 0 else h y.val)) := by
  intro l _ r N L hL ξ hξ h hh
  have hM : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have hξ1 : ‖ξ‖ = 1 := by
    have h1 : ‖ξ‖ ^ (l ^ r) = 1 := by rw [← norm_pow, hξ.pow_eq_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hM.ne').1 h1
  unfold Cg
  rw [← Nat.cast_pow, ← exact_sum hM hξ N l h, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun x _ => ?_)
  rw [← mul_sub, GlobalTheory.KZ.mass, ← Finset.sum_sub_distrib, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (hh x)).trans ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun k _ => ?_)
  rw [← mul_sub, norm_mul, norm_pow, hξ1, one_pow, one_mul]
  exact hL (ξ ^ k) (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow])
