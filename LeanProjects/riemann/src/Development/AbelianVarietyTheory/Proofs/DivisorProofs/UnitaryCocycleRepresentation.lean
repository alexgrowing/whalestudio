import Mathlib

namespace GlobalTheory

theorem matrices_unitary_hom_of_linearIndependent :
    ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ), (1 : G) ∈ K → (∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) → (∀ k ∈ K, k⁻¹ ∈ K) → LinearIndependent ℂ b → (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) → (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) → A 1 = 1 ∧ (∀ k ∈ K, ∀ k' ∈ K, A (k * k') = A k * A k') ∧ ∀ k ∈ K, A k⁻¹ = star (A k) := by
  intro G _ K V _ _ ρ m b A h1 hmul hinv hb hA hU
  have key : ∀ M N : Matrix (Fin m) (Fin m) ℂ,
      (∀ j, ∑ i, M i j • b i = ∑ i, N i j • b i) → M = N := by
    intro M N h
    ext i j
    have := Fintype.linearIndependent_iff.mp hb (fun i => M i j - N i j)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h j, sub_self]) i
    exact sub_eq_zero.mp this
  have hA1 : A 1 = 1 := by
    apply key
    intro j
    rw [← hA 1 h1 j, map_one]
    simp [Matrix.one_apply]
  have hmul' : ∀ k ∈ K, ∀ k' ∈ K, A (k * k') = A k * A k' := by
    intro k hk k' hk'
    apply key
    intro j
    rw [← hA _ (hmul k hk k' hk') j, map_mul, Module.End.mul_apply, hA k' hk' j, map_sum]
    simp only [map_smul, hA k hk, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  refine ⟨hA1, hmul', ?_⟩
  intro k hk
  have e : A k⁻¹ * A k = 1 := by
    rw [← hmul' _ (hinv k hk) k hk, inv_mul_cancel, hA1]
  have u : A k * star (A k) = 1 := Matrix.mem_unitaryGroup_iff.mp (hU k hk)
  calc A k⁻¹ = A k⁻¹ * (A k * star (A k)) := by rw [u, Matrix.mul_one]
    _ = star (A k) := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

end GlobalTheory
