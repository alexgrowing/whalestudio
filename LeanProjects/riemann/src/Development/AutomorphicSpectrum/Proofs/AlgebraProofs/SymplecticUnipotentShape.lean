import Mathlib
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem symplectic_unipotent_shape : ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ), (∀ x, B x x = 0) → (∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 ∧ B (bas (.inr i)) (bas (.inr j)) = 0 ∧ B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0) → ∀ T : Λ →ₗ[ℤ] Λ, (∀ x y, B (T x) (T y) = B x y) → (∀ i, T (bas (.inl i)) = bas (.inl i)) → ∃ N : Matrix (Fin g) (Fin g) ℤ, Nᵀ = N ∧ ∀ j, T (bas (.inr j)) = bas (.inr j) + ∑ k, N j k • bas (.inl k) := by
  intro g Λ _ B bas halt hB T hT hTa
  have hB1 : ∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 := fun i j => (hB i j).1
  have hB2 : ∀ i j, B (bas (.inr i)) (bas (.inr j)) = 0 := fun i j => (hB i j).2.1
  have hB3 : ∀ i j, B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0 :=
    fun i j => (hB i j).2.2
  have skew : ∀ x y, B x y = -B y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    linarith
  have hexp : ∀ v : Λ, v = ∑ k, bas.repr v (.inl k) • bas (.inl k) +
      ∑ k, bas.repr v (.inr k) • bas (.inr k) := by
    intro v
    conv_lhs => rw [← bas.sum_repr v]
    rw [Fintype.sum_sum_type]
  have pa : ∀ i v, B (bas (.inl i)) v = bas.repr v (.inr i) := by
    intro i v
    conv_lhs => rw [hexp v]
    simp [hB1, hB3]
  have pb : ∀ i v, B (bas (.inr i)) v = -bas.repr v (.inl i) := by
    intro i v
    have hba : ∀ k, B (bas (.inr i)) (bas (.inl k)) = -(if k = i then 1 else 0) :=
      fun k => by rw [skew, hB3]
    conv_lhs => rw [hexp v]
    simp [hba, hB2]
  have hd : ∀ i j, bas.repr (T (bas (.inr j))) (.inr i) = if i = j then 1 else 0 := by
    intro i j
    rw [← pa, ← hTa i, hT, hB3]
  have hTb : ∀ j, T (bas (.inr j)) =
      bas (.inr j) + ∑ k, bas.repr (T (bas (.inr j))) (.inl k) • bas (.inl k) := by
    intro j
    conv_lhs => rw [hexp (T (bas (.inr j)))]
    rw [add_comm]
    congr 1
    simp [hd, ite_smul]
  refine ⟨fun j k => bas.repr (T (bas (.inr j))) (.inl k), ?_, hTb⟩
  ext i j
  show bas.repr (T (bas (.inr j))) (.inl i) = bas.repr (T (bas (.inr i))) (.inl j)
  have h0 : B (T (bas (.inr j))) (T (bas (.inr i))) = 0 := by rw [hT, hB2]
  rw [hTb j, map_add, LinearMap.add_apply, pb j] at h0
  simp [map_sum, LinearMap.sum_apply, pa, hd] at h0
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
