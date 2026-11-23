import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory

theorem matrix_exists_sub_mem_trace_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Submodule ℂ (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ n ∈ N, (nᴴ * M₀).trace = 0 := by
  let e : Matrix ι ι ℂ →ₗ[ℂ] EuclideanSpace ℂ (ι × ι) :=
    { toFun := fun A => WithLp.toLp 2 (fun p : ι × ι => A p.1 p.2)
      map_add' := fun A B => rfl
      map_smul' := fun c A => rfl }
  have hin : ∀ A B : Matrix ι ι ℂ, inner ℂ (e A) (e B) = (Aᴴ * B).trace := by
    intro A B
    simp only [e, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
    rfl
  obtain ⟨y, hy, z, hz, h⟩ := (N.map e).exists_add_mem_mem_orthogonal (e M)
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨M - y', by simpa using hy', fun n hn => ?_⟩
  rw [← hin, map_sub, h, add_sub_cancel_left]
  exact (Submodule.mem_orthogonal _ _).1 hz _ ⟨n, hn, rfl⟩

theorem matrix_commutant_lift_mod_stable :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ))
      (N : Submodule ℂ (Matrix ι ι ℂ)), (∀ x ∈ S, xᴴ ∈ S) →
      (∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N) → ∀ M : Matrix ι ι ℂ,
      (∀ x ∈ S, x * M - M * x ∈ N) →
      ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ x ∈ S, x * M₀ = M₀ * x := by
  intro ι _ _ S N hS hN M hM
  obtain ⟨M₀, h1, h2⟩ := matrix_exists_sub_mem_trace_orthogonal N M
  refine ⟨M₀, h1, fun x hx => ?_⟩
  have hw : x * M₀ - M₀ * x ∈ N := by
    have := N.sub_mem (hM x hx) (hN x hx _ h1)
    convert this using 1
    noncomm_ring
  set w := x * M₀ - M₀ * x with hwdef
  have h3 := h2 _ (hN _ (hS x hx) w hw)
  have h4 : (wᴴ * w).trace = 0 := by
    rw [← h3]
    have : (wᴴ * (M₀ * x)).trace = (x * wᴴ * M₀).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    conv_lhs => rw [hwdef, Matrix.mul_sub, ← hwdef]
    rw [Matrix.trace_sub, this]
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc]
  open scoped ComplexOrder in
  exact sub_eq_zero.1 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h4)

end GlobalTheory
