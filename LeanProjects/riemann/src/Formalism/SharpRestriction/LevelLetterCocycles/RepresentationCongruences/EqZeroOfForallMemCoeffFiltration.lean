import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS

open PowerSeries

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

def T (O : Type*) [CommRing O] [IsLocalRing O] (N : ℕ) : Ideal O⟦X⟧ where
  carrier := {x | ∀ m, coeff m x ∈ (IsLocalRing.maximalIdeal O) ^ (N - m)}
  add_mem' {a b} ha hb m := by
    simpa only [map_add] using Ideal.add_mem _ (ha m) (hb m)
  zero_mem' m := by simp
  smul_mem' c x hx m := by
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ ?_
    have h2 : p.2 ≤ m := by have := Finset.mem_antidiagonal.mp hp; omega
    exact Ideal.pow_le_pow_right (by omega) (hx p.2)

theorem mem_T {N : ℕ} {x : O⟦X⟧} :
    x ∈ T O N ↔ ∀ m, coeff m x ∈ (IsLocalRing.maximalIdeal O) ^ (N - m) := Iff.rfl

theorem T_anti {N N' : ℕ} (h : N ≤ N') : T O N' ≤ T O N := by
  intro x hx
  rw [mem_T] at hx ⊢
  exact fun m => Ideal.pow_le_pow_right (by omega) (hx m)

theorem T_mul {a b : ℕ} {x y : O⟦X⟧} (hx : x ∈ T O a) (hy : y ∈ T O b) : x * y ∈ T O (a + b) := by
  rw [mem_T] at hx hy ⊢
  intro m
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have h := Finset.mem_antidiagonal.mp hp
  have h2 := Ideal.mul_mem_mul (hx p.1) (hy p.2)
  rw [← pow_add] at h2
  exact Ideal.pow_le_pow_right (by omega) h2

private theorem maximalIdeal_pow_smul_whole_ring_eq_self (n : ℕ) :
    ((IsLocalRing.maximalIdeal O) ^ n • ⊤ : Submodule O O) = (IsLocalRing.maximalIdeal O) ^ n := by
  first
    | rw [Ideal.smul_eq_mul, Ideal.mul_top]
    | simp [Ideal.smul_eq_mul]
    | simp

theorem eq_zero_of_forall_mem_coeffFiltration {x : O⟦X⟧} (hx : ∀ N, x ∈ T O N) : x = 0 := by
  have H : IsHausdorff (IsLocalRing.maximalIdeal O) O := inferInstance
  ext m
  rw [map_zero]
  refine H.haus _ fun n => ?_
  rw [SModEq.zero, maximalIdeal_pow_smul_whole_ring_eq_self]
  have h := (mem_T.mp (hx (n + m))) m
  rwa [Nat.add_sub_cancel] at h

variable {g : O⟦X⟧}

theorem mem_T_one (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : g ∈ T O 1 := by
  rw [mem_T]
  intro m
  rcases m with _ | m
  · rw [Nat.sub_zero, pow_one, coeff_zero_eq_constantCoeff_apply]
    exact hg
  · rw [show 1 - (m + 1) = 0 by omega, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem pow_mem_coeffFiltration (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (N : ℕ) : g ^ N ∈ T O N := by
  induction N with
  | zero =>
    rw [pow_zero, mem_T]
    intro m
    rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    rw [pow_succ]
    exact T_mul ih (mem_T_one hg)

theorem aeval_mem_coeffFiltration (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) {N : ℕ} {p : Polynomial O}
    (hp : ∀ d < N, p.coeff d = 0) : Polynomial.aeval g p ∈ T O N := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d < N
  · rw [hp d hd, zero_smul]
    exact Submodule.zero_mem _
  · rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _
      (T_anti (not_lt.mp hd) (pow_mem_coeffFiltration hg d))

noncomputable def S (g : O⟦X⟧) (N : ℕ) (f : O⟦X⟧) : O⟦X⟧ := Polynomial.aeval g (trunc N f)

theorem S_sub_mem (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) {N N' : ℕ}
    (h : N ≤ N') : S g N' f - S g N f ∈ T O N := by
  unfold S
  rw [← map_sub (Polynomial.aeval (R := O) g)]
  refine aeval_mem_coeffFiltration hg fun d hd => ?_
  have hd' : d < N' := lt_of_lt_of_le hd h
  simp [coeff_trunc, hd, hd']

theorem exists_lim (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) (m : ℕ) :
    ∃ L : O, ∀ N, coeff m (S g N f) - L ∈ (IsLocalRing.maximalIdeal O) ^ (N - m) := by
  have hC : IsPrecomplete (IsLocalRing.maximalIdeal O) O := inferInstance
  obtain ⟨L, hL⟩ := hC.prec (f := fun k => coeff m (S g (k + m) f)) (fun {a b} hab => by
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_whole_ring_eq_self]
    have h1 := S_sub_mem hg f (show a + m ≤ b + m by omega) m
    rw [map_sub, Nat.add_sub_cancel] at h1
    have h2 := neg_mem h1
    rw [neg_sub] at h2
    exact h2)
  refine ⟨L, fun N => ?_⟩
  rcases le_or_gt m N with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    have h3 := hL k
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_whole_ring_eq_self] at h3
    rw [Nat.add_sub_cancel]
    exact h3
  · rw [Nat.sub_eq_zero_of_le h.le, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

noncomputable def subst (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) : O⟦X⟧ :=
  PowerSeries.mk fun m => Classical.choose (exists_lim hg f m)

theorem subst_sub_mem (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) (N : ℕ) :
    subst hg f - S g N f ∈ T O N := by
  rw [mem_T]
  intro m
  rw [map_sub]
  simp only [subst, coeff_mk]
  have h1 := Classical.choose_spec (exists_lim hg f m) N
  have h2 := neg_mem h1
  rwa [neg_sub] at h2

theorem subst_eq (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f y : O⟦X⟧) (N0 : ℕ)
    (hy : ∀ N, N0 ≤ N → y - S g N f ∈ T O N) : y = subst hg f := by
  have key : ∀ N, y - subst hg f ∈ T O N := fun N => by
    have h1 := hy (N + N0) (by omega)
    have h2 := subst_sub_mem hg f (N + N0)
    have h3 := sub_mem h1 h2
    rw [sub_sub_sub_cancel_right] at h3
    exact T_anti (by omega) h3
  exact sub_eq_zero.mp (eq_zero_of_forall_mem_coeffFiltration key)

private theorem truncEval_add (N : ℕ) (f f' : O⟦X⟧) :
    S g N (f + f') = S g N f + S g N f' := by
  have h : trunc N (f + f') = trunc N f + trunc N f' := map_add (trunc N) f f'
  simp only [S, h, map_add]

theorem subst_add (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f f' : O⟦X⟧) :
    subst hg (f + f') = subst hg f + subst hg f' := by
  refine (subst_eq hg (f + f') _ 0 fun N _ => ?_).symm
  rw [truncEval_add, add_sub_add_comm]
  exact add_mem (subst_sub_mem hg f N) (subst_sub_mem hg f' N)

private theorem truncEval_smul (N : ℕ) (r : O) (f : O⟦X⟧) :
    S g N (r • f) = r • S g N f := by
  have h : trunc N (r • f) = r • trunc N f := by
    first
      | exact map_smul (trunc N) r f
      | (ext d; simp only [coeff_trunc, Polynomial.coeff_smul, coeff_smul]; split_ifs <;> simp)
  simp only [S, h, map_smul]

theorem subst_smul (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (r : O) (f : O⟦X⟧) :
    subst hg (r • f) = r • subst hg f := by
  refine (subst_eq hg (r • f) _ 0 fun N _ => ?_).symm
  rw [truncEval_smul, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ r (subst_sub_mem hg f N)

private theorem coeff_trunc_mul_trunc_of_lt {N d : ℕ} (hd : d < N) (f f' : O⟦X⟧) :
    (trunc N f * trunc N f').coeff d = coeff d (f * f') := by
  rw [Polynomial.coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.mem_antidiagonal.mp hx
  have h1 : x.1 < N := by omega
  have h2 : x.2 < N := by omega
  simp [coeff_trunc, h1, h2]

theorem subst_mul (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f f' : O⟦X⟧) :
    subst hg (f * f') = subst hg f * subst hg f' := by
  refine (subst_eq hg (f * f') _ 0 fun N _ => ?_).symm
  have hA := subst_sub_mem hg f N
  have hB := subst_sub_mem hg f' N
  have hT : S g N f * S g N f' - S g N (f * f') ∈ T O N := by
    unfold S
    rw [← map_mul (Polynomial.aeval (R := O) g), ← map_sub (Polynomial.aeval (R := O) g)]
    refine aeval_mem_coeffFiltration hg fun d hd => ?_
    rw [Polynomial.coeff_sub, coeff_trunc_mul_trunc_of_lt hd]
    simp [coeff_trunc, hd]
  have key : subst hg f * subst hg f' - S g N (f * f') =
      (subst hg f - S g N f) * subst hg f' +
        S g N f * (subst hg f' - S g N f') +
        (S g N f * S g N f' - S g N (f * f')) := by ring
  rw [key]
  exact add_mem (add_mem (Ideal.mul_mem_right _ _ hA) (Ideal.mul_mem_left _ _ hB)) hT

theorem subst_one (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : subst hg (1 : O⟦X⟧) = 1 := by
  refine (subst_eq hg 1 1 1 fun N hN => ?_).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [S, trunc_one, map_one, sub_self]
  exact Submodule.zero_mem _

theorem subst_X (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : subst hg (X : O⟦X⟧) = g := by
  refine (subst_eq hg X g 2 fun N hN => ?_).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [S, trunc_X, Polynomial.aeval_X, sub_self]
  exact Submodule.zero_mem _

noncomputable def substAlgHom (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : O⟦X⟧ →ₐ[O] O⟦X⟧ :=
  AlgHom.ofLinearMap
    { toFun := subst hg
      map_add' := subst_add hg
      map_smul' := subst_smul hg }
    (subst_one hg) (subst_mul hg)

theorem exists_algHom_X_eq (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) :
    ∃ h : O⟦X⟧ →ₐ[O] O⟦X⟧, h X = g := ⟨substAlgHom hg, subst_X hg⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS
