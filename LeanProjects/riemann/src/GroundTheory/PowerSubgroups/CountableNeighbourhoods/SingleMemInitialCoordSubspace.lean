import Mathlib

namespace GroundTheory.Variant₂.N1

def initialCoordSubspace {K : Type*} [Field K] {n : ℕ} (k : ℕ) : Submodule K (Fin n → K) where
  carrier := {v | ∀ i : Fin n, k ≤ (i : ℕ) → v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

theorem mem_initialCoordSubspace {K : Type*} [Field K] {n k : ℕ} (v : Fin n → K) :
    v ∈ (initialCoordSubspace k : Submodule K (Fin n → K)) ↔ ∀ i : Fin n, k ≤ (i : ℕ) → v i = 0 :=
  Iff.rfl

theorem single_mem_initialCoordSubspace {K : Type*} [Field K] {n k : ℕ} {j : Fin n} (hj : (j : ℕ) < k)
    (c : K) : Pi.single j c ∈ (initialCoordSubspace k : Submodule K (Fin n → K)) := by
  intro i hi
  have : i ≠ j := by
    intro h; subst h; omega
  simp [this]

theorem finrank_initialCoordSubspace {K : Type*} [Field K] {n k : ℕ} (h : k ≤ n) :
    Module.finrank K (initialCoordSubspace k : Submodule K (Fin n → K)) = k := by
  let P : (Fin n → K) →ₗ[K] ({i : Fin n // k ≤ (i : ℕ)} → K) :=
    LinearMap.pi (fun i => LinearMap.proj i.1)
  have hker : LinearMap.ker P = initialCoordSubspace k := by
    ext v
    simp only [LinearMap.mem_ker, mem_initialCoordSubspace]
    constructor
    · intro hv i hi
      exact congrFun hv ⟨i, hi⟩
    · intro hv
      funext i
      exact hv i.1 i.2
  have hsurj : Function.Surjective P := by
    intro f
    refine ⟨fun i => if hi : k ≤ (i : ℕ) then f ⟨i, hi⟩ else 0, ?_⟩
    funext i
    simp [P, i.2]
  have hrange : LinearMap.range P = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have key := LinearMap.finrank_range_add_finrank_ker P
  rw [hrange, finrank_top, hker, Module.finrank_fin_fun,
    Module.finrank_fintype_fun_eq_card] at key
  have e : {i : Fin n // (i : ℕ) < k} ≃ Fin k :=
    { toFun := fun i => ⟨i.1, i.2⟩
      invFun := fun j => ⟨⟨j, lt_of_lt_of_le j.2 h⟩, j.2⟩
      left_inv := fun i => rfl
      right_inv := fun j => rfl }
  have hc1 : Fintype.card {i : Fin n // (i : ℕ) < k} = k := by
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hc2 : Fintype.card {i : Fin n // k ≤ (i : ℕ)} =
      Fintype.card {i : Fin n // ¬ ((i : ℕ) < k)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun i => not_lt.symm))
  have hc3 := Fintype.card_subtype_compl (fun i : Fin n => (i : ℕ) < k)
  rw [Fintype.card_fin] at hc3
  have hle : Fintype.card {i : Fin n // (i : ℕ) < k} ≤ n := by omega
  omega

end GroundTheory.Variant₂.N1
