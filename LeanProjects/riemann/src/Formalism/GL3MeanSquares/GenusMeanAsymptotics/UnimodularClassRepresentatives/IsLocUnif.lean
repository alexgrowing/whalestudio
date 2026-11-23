import Mathlib

open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K]

structure IsLocUnif (S : Subring K) (ϖ : K) : Prop where
  star_mem : ∀ a ∈ S, star a ∈ S
  mem : ϖ ∈ S
  fix : star ϖ = ϖ
  ne : ϖ ≠ 0
  tr : ∃ τ ∈ S, τ + star τ = 1
  skew : ∃ θ ∈ S, star θ = -θ ∧ θ ≠ 0
  dv : ∀ f ∈ S, star f = f → f⁻¹ ∈ S ∨ f * ϖ⁻¹ ∈ S
  rad : ∀ s ∈ S, 1 + ϖ * s ≠ 0 ∧ (1 + ϖ * s)⁻¹ ∈ S
  arch : ∀ a : K, ∃ l : ℕ, ϖ ^ l * a ∈ S

def Ent (S : Subring K) {m n : Type*} (M : Matrix m n K) : Prop := ∀ i j, M i j ∈ S

variable {S : Subring K} {m n o : Type*}

theorem Ent.add {M N : Matrix m n K} (hM : Ent S M) (hN : Ent S N) : Ent S (M + N) := by
  exact fun i j => S.add_mem (hM i j) (hN i j)

theorem Ent.sub {M N : Matrix m n K} (hM : Ent S M) (hN : Ent S N) : Ent S (M - N) := by
  exact fun i j => S.sub_mem (hM i j) (hN i j)

theorem Ent.neg {M : Matrix m n K} (hM : Ent S M) : Ent S (-M) := by
  exact fun i j => S.neg_mem (hM i j)

theorem Ent.zero : Ent S (0 : Matrix m n K) := by
  exact fun _ _ => S.zero_mem

theorem Ent.smul {a : K} (ha : a ∈ S) {M : Matrix m n K} (hM : Ent S M) : Ent S (a • M) := by
  exact fun i j => S.mul_mem ha (hM i j)

theorem Ent.mul [Fintype n] {M : Matrix m n K} {N : Matrix n o K} (hM : Ent S M) (hN : Ent S N) :
    Ent S (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => S.mul_mem (hM i k) (hN k j)

theorem Ent.one [DecidableEq n] : Ent S (1 : Matrix n n K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem Ent.conjTranspose (hS : ∀ a ∈ S, star a ∈ S) {M : Matrix m n K} (hM : Ent S M) : Ent S Mᴴ := by
  exact fun i j => hS _ (hM j i)

theorem Ent.exists_map {M : Matrix m n K} (hM : Ent S M) :
    ∃ M₀ : Matrix m n S, M₀.map S.subtype = M := by
  refine ⟨fun i j => ⟨M i j, hM i j⟩, ?_⟩
  ext i j
  rfl

theorem Ent.det [Fintype n] [DecidableEq n] {M : Matrix n n K} (hM : Ent S M) : M.det ∈ S := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  have h := RingHom.map_det S.subtype M₀
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (M₀.det).2

theorem Ent.adjugate [Fintype n] [DecidableEq n] {M : Matrix n n K} (hM : Ent S M) :
    Ent S M.adjugate := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  have h := RingHom.map_adjugate S.subtype M₀
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [← h]
  intro i j
  exact (M₀.adjugate i j).2

theorem pow_mem {ϖ : K} (hS : IsLocUnif S ϖ) (k : ℕ) : ϖ ^ k ∈ S := by
  exact S.pow_mem hS.mem k

end Formalism.HermitianLattices.Ext.L3.HU
