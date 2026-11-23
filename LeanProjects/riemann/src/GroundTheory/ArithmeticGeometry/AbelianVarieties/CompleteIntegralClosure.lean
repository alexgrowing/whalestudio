import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing

section Basis

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]

theorem mem_ideal_smul_top_self_iff (J : Ideal R) (a : R) :
    a ∈ (J • ⊤ : Submodule R R) ↔ a ∈ J := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem mem_ideal_smul_top_iff_repr (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ (J • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  classical
  have := Fintype.ofFinite ι
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · rw [map_add, Finsupp.add_apply]
      exact J.add_mem hx hy
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isPrecomplete_of_basis (I : Ideal R) [IsPrecomplete I R] (b : Module.Basis ι R M) :
    IsPrecomplete I M := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ c : R, ∀ n, b.repr (f n) i ≡ c [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec inferInstance fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_ideal_smul_top_iff_repr b] at h
      rw [SModEq.sub_mem, mem_ideal_smul_top_self_iff]
      simpa using h i
  choose c hc using hc
  refine ⟨∑ i, c i • b i, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_ideal_smul_top_iff_repr b]
  intro i
  have h := hc i n
  rw [SModEq.sub_mem, mem_ideal_smul_top_self_iff] at h
  simpa [b.repr_sum_self, Finsupp.single_apply] using h

end Basis

section Transfer

variable {R : Type*} [CommRing R]

end Transfer

section Idempotent

variable {B : Type*} [CommRing B]

def idemIter (x : B) : ℕ → B
  | 0 => x
  | n + 1 => 3 * idemIter x n ^ 2 - 2 * idemIter x n ^ 3

variable (J : Ideal B) [IsPrecomplete J B] [IsHausdorff J B]

end Idempotent

section IntegralClosure

variable (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra 𝒪 L] [IsScalarTower 𝒪 K L]

include K

end IntegralClosure

end

end GroundTheory.Arith.Abelian
