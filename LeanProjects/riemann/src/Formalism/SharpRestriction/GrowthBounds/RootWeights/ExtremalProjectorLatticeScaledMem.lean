import Formalism.SharpRestriction.GrowthBounds.RootWeights.DvrFractionFieldCharZeroPrime

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Wt

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem operator_pow_shifts_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (a b : Fin n) (ν : Fin n → ℤ) (k : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : ((E a b) ^ k) x ∈ weightSp E (ν + (k : ℤ) • rootW a b) := by
  unfold OperatorsShiftWeightsByRoots at hs
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h1 := hs a b _ _ ih
    convert h1 using 2
    rw [Nat.cast_succ, add_smul, one_smul, add_assoc]

theorem divided_power_shifts_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (a b : Fin n) (ν : Fin n → ℤ) (k : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : divPowE E a b k x ∈ weightSp E (ν + (k : ℤ) • rootW a b) := by
  unfold divPowE
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (operator_pow_shifts_weight hs a b ν k x hx)

theorem rootWeight_swap_neg (a b : Fin n) : rootW b a = - rootW a b := by
  unfold rootW
  rw [neg_sub]

end Wt

section Lattice

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem projector_factor_lattice_scaled_mem (S : UniformizedDVR p O) (hp : p.Prime) {E : GLOps n (KK O) V} (hs : OperatorsShiftWeightsByRoots E)
    {M : Submodule O V} (hM : UZStable (O := O) E M) (L : ℕ)
    (hL : ∀ (k : ℕ) (a b : Fin n), a ≠ b → weightSp E 0 ≠ ⊥ → weightSp E ((k : ℤ) • rootW a b) ≠ ⊥ → k ≤ L)
    (a b : Fin n) (hab : a < b) (T : ℕ) (y : V) (hy : y ∈ M) (hy0 : y ∈ weightSp E 0) :
    ((p : O) ^ (deF p n L)) • ppFac E 0 a b T y ∈ M ∧ ppFac E 0 a b T y ∈ weightSp E 0 := by
  have hcz := dvr_fraction_field_charZero_prime S hp
  have hz : ∀ k, divPowE E b a k (divPowE E a b k y) ∈ weightSp E 0 := by
    intro k
    have h1 := divided_power_shifts_weight hs a b 0 k y hy0
    have h2 := divided_power_shifts_weight hs b a _ k _ h1
    convert h2 using 2
    rw [rootWeight_swap_neg a b]
    simp
  have hzM : ∀ k, divPowE E b a k (divPowE E a b k y) ∈ M := fun k =>
    hM _ (Or.inl ⟨b, a, k, hab.ne', rfl⟩) _ (hM _ (Or.inl ⟨a, b, k, hab.ne, rfl⟩) _ hy)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = ((0 : Fin n → ℤ) a - (0 : Fin n → ℤ) b + ((b : ℤ) - (a : ℤ))).toNat := ⟨_, rfl⟩
  have htn : t + 1 ≤ n := by
    have h1 : (a : ℕ) < (b : ℕ) := hab
    have h2 := b.isLt
    simp only [Pi.zero_apply] at ht
    omega
  have hexp : ppFac E 0 a b T y = ∑ k ∈ range (T + 1),
      ((-1 : KK O) ^ k / ((Nat.choose (t + k) k : ℕ) : KK O)) • divPowE E b a k (divPowE E a b k y) := by
    rw [ht]
    simp [ppFac, LinearMap.sum_apply]
  constructor
  · rw [hexp, Finset.smul_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases h0 : divPowE E a b k y = 0
    · rw [h0]; simp
    · have hy1 : y ≠ 0 := by
        rintro rfl
        exact h0 (map_zero _)
      have hk : k ≤ L := by
        refine hL k a b hab.ne ((Submodule.ne_bot_iff _).2 ⟨y, hy0, hy1⟩)
          ((Submodule.ne_bot_iff _).2 ⟨_, ?_, h0⟩)
        have := divided_power_shifts_weight hs a b 0 k y hy0
        rwa [zero_add] at this
      have hlog : (Nat.choose (t + k) k).factorization p ≤ deF p n L :=
        (Nat.factorization_choose_le_log).trans (Nat.log_mono_right (by omega))
      obtain ⟨o, ho⟩ := exists_mul_natCast_eq_prime_pow S hp (Nat.choose_pos (Nat.le_add_left k t)).ne' hlog
      have hC : ((Nat.choose (t + k) k : ℕ) : KK O) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_left k t)).ne'
      have hK : algebraMap O (KK O) ((p : O) ^ deF p n L) *
          ((-1 : KK O) ^ k / ((Nat.choose (t + k) k : ℕ) : KK O)) = algebraMap O (KK O) ((-1) ^ k * o) := by
        rw [← ho]
        simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
        field_simp
      rw [← algebraMap_smul (KK O) ((p : O) ^ deF p n L), smul_smul, hK, algebraMap_smul]
      exact M.smul_mem _ (hzM k)
  · rw [hexp]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hz k)

theorem extremal_projector_lattice_scaled_mem (S : UniformizedDVR p O) (hp : p.Prime) {E : GLOps n (KK O) V} (hs : OperatorsShiftWeightsByRoots E)
    {M : Submodule O V} (hM : UZStable (O := O) E M) (L : ℕ)
    (hL : ∀ (k : ℕ) (a b : Fin n), a ≠ b → weightSp E 0 ≠ ⊥ → weightSp E ((k : ℤ) • rootW a b) ≠ ⊥ → k ≤ L)
    (ord : List (Fin n × Fin n)) (hord : ∀ ab ∈ ord, ab.1 < ab.2) (T : ℕ) (y : V) (hy : y ∈ M)
    (hy0 : y ∈ weightSp E 0) :
    ((p : O) ^ (ord.length * deF p n L)) • pp E 0 ord T y ∈ M ∧ pp E 0 ord T y ∈ weightSp E 0 := by
  induction ord with
  | nil => simpa [pp] using ⟨hy, hy0⟩
  | cons ab t ih =>
    obtain ⟨h1, h2⟩ := ih (fun x hx => hord x (List.mem_cons_of_mem _ hx))
    have hpp : pp E 0 (ab :: t) T y = ppFac E 0 ab.1 ab.2 T (pp E 0 t T y) := by simp [pp]
    have h3 := projector_factor_lattice_scaled_mem S hp hs hM L hL ab.1 ab.2 (hord ab List.mem_cons_self) T _ h1
      ((weightSp E 0).smul_of_tower_mem _ h2)
    have h4 := projector_factor_lattice_scaled_mem S hp hs (M := ⊤) (fun _ _ _ _ => Submodule.mem_top) L hL ab.1 ab.2
      (hord ab List.mem_cons_self) T _ Submodule.mem_top h2
    refine ⟨?_, by rw [hpp]; exact h4.2⟩
    have h5 := h3.1
    rw [LinearMap.map_smul_of_tower, smul_smul, ← pow_add] at h5
    rw [hpp, List.length_cons, show (t.length + 1) * deF p n L = deF p n L + t.length * deF p n L by ring]
    exact h5

theorem binomial_subring_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    (u : Module.End (KK O) V) (hu : u ∈ binomialDiagonalSubring E) : ∀ x ∈ M, u x ∈ M := by
  unfold binomialDiagonalSubring at hu
  unfold UZStable at hM
  induction hu using Subring.closure_induction with
  | mem u hu => obtain ⟨a, k, rfl⟩ := hu; exact hM _ (Or.inr ⟨a, k, rfl⟩)
  | zero => intro x _; simp
  | one => intro x hx; simpa using hx
  | add u v _ _ hu hv => intro x hx; rw [LinearMap.add_apply]; exact M.add_mem (hu x hx) (hv x hx)
  | neg u _ hu => intro x hx; rw [LinearMap.neg_apply]; exact M.neg_mem (hu x hx)
  | mul u v _ _ hu hv => intro x hx; rw [Module.End.mul_apply]; exact hu _ (hv x hx)

end Lattice

end Formalism.MainNotions.G.GLWeightTheory
