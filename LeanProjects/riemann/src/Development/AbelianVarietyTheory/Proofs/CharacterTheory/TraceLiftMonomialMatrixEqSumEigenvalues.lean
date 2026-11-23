import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinrankEigenspaceMonomialMatrixLiftStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumCharpolyRootsEqFinsumEigenspaceFinrankStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.MonoTrace

theorem ncard_pow_eq_one (k : Type) [Field k] [IsAlgClosed k] (N : ℕ) (hN : (N : k) ≠ 0) :
    {μ : k | μ ^ N = 1}.Finite ∧ {μ : k | μ ^ N = 1}.ncard = N := by
  haveI : NeZero (N : k) := ⟨hN⟩
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  have hs : {μ : k | μ ^ N = 1} = (nthRootsFinset N (1 : k) : Set k) := by
    ext x
    simp [mem_nthRootsFinset (Nat.pos_of_ne_zero hN0)]
  rw [hs]
  exact ⟨Finset.finite_toSet _, by rw [Set.ncard_coe_finset, hζ.card_nthRootsFinset]⟩

theorem bijOn_pow_eq_one (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (N : ℕ) (hN : (N : k) ≠ 0) :
    Set.BijOn θ {μ : k | μ ^ N = 1} {μ : ℂ | μ ^ N = 1} := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hne : ∀ μ : k, μ ^ N = 1 → μ ≠ 0 := by
    rintro μ h rfl
    simp [hN0] at h
  have hmaps : Set.MapsTo θ {μ : k | μ ^ N = 1} {μ : ℂ | μ ^ N = 1} := by
    intro μ h
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [← map_pow, h, map_one]
  have hinj : Set.InjOn θ {μ : k | μ ^ N = 1} :=
    fun x hx y hy h => hθ x y (hne x hx) (hne y hy) h
  obtain ⟨_, h1⟩ := ncard_pow_eq_one k N hN
  obtain ⟨f2, h2⟩ := ncard_pow_eq_one ℂ N (by exact_mod_cast hN0)
  have himg : θ '' {μ : k | μ ^ N = 1} = {μ : ℂ | μ ^ N = 1} := by
    apply Set.eq_of_subset_of_ncard_le hmaps.image_subset _ f2
    rw [hinj.ncard_image, h1, h2]
  exact ⟨hmaps, hinj, himg.ge⟩

theorem trace_lift_monomial : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n N : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → (N : k) ≠ 0 → (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k) ^ N = 1 → (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) ^ N = 1 → Matrix.trace (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) = ((Matrix.charpoly (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k)).roots.map θ).sum := by
  intro k _ _ θ hθ n N σ c hc hN hA hB
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hE := GlobalTheory.T.finrank_eigenspace_monomial_matrix_lift k θ hθ n σ c hc
  set A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => if i = σ j then c j else 0 with hAdef
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if i = σ j then θ (c j) else 0 with hBdef
  have h1 := GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank k (Fin n → k) (Matrix.toLin' A) N hN
    (by rw [← Matrix.toLin'_pow, hA, Matrix.toLin'_one]; rfl) θ
  have h2 := GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank ℂ (Fin n → ℂ) (Matrix.toLin' B) N (by exact_mod_cast hN0)
    (by rw [← Matrix.toLin'_pow, hB, Matrix.toLin'_one]; rfl) id
  rw [Matrix.charpoly_toLin'] at h1 h2
  rw [Matrix.trace_eq_sum_roots_charpoly, h1]
  rw [Multiset.map_id] at h2
  rw [h2]
  symm
  apply finsum_mem_eq_of_bijOn θ (bijOn_pow_eq_one k θ hθ N hN)
  intro μ hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp [hN0] at hμ
  rw [hE μ hμ0]
  rfl

end GlobalTheory.MonoTrace
