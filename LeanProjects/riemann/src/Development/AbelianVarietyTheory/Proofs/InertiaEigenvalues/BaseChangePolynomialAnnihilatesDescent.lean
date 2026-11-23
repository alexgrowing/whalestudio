import Mathlib
open Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem baseChange_polynomial_kills_descent (Ks L0 KB WK ι : Type) [Field Ks] [Field L0] [Field KB]
    [Algebra Ks L0] [Algebra Ks KB] [AddCommGroup WK]
    [Module Ks WK] (rd : L0 →+* KB) (hrd : ∀ a : Ks, rd (algebraMap Ks L0 a) = algebraMap Ks KB a)
    (T0 : Module.End Ks WK) (s : Finset ι) (ρ : ι → Module.End Ks WK) (a : ι → L0) (q : L0[X])
    (hq : ∀ z ∈ LinearMap.range (∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)),
      Polynomial.aeval (LinearMap.baseChange L0 T0) q z = 0) :
    ∀ y ∈ LinearMap.range (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)),
      Polynomial.aeval (LinearMap.baseChange KB T0) (q.map rd) y = 0 := by
  classical

  let rdL : L0 →ₗ[Ks] KB :=
    { toFun := rd
      map_add' := rd.map_add
      map_smul' := fun c x => by
        simp only [Algebra.smul_def, map_mul, hrd, RingHom.id_apply] }
  let R : L0 ⊗[Ks] WK →ₗ[Ks] KB ⊗[Ks] WK := LinearMap.rTensor WK rdL
  have hRt : ∀ (c : L0) (w : WK), R (c ⊗ₜ[Ks] w) = rd c ⊗ₜ[Ks] w := fun c w => rfl

  have hRs : ∀ (c : L0) (z : L0 ⊗[Ks] WK), R (c • z) = rd c • R z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => simp [TensorProduct.smul_tmul', hRt]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

  set B0 := LinearMap.baseChange L0 T0 with hB0
  set B := LinearMap.baseChange KB T0 with hB
  have hRB : ∀ z, R (B0 z) = B (R z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => simp [hB0, hB, hRt]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hRpow : ∀ (n : ℕ) z, R ((B0 ^ n) z) = (B ^ n) (R z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hRB]
  have hRq : ∀ (p : L0[X]) z, Polynomial.aeval B (p.map rd) (R z) = R (Polynomial.aeval B0 p z) := by
    intro p z
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hr]
    | monomial n c =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      simp only [Module.End.mul_apply, Module.algebraMap_end_apply, hRs, hRpow]

  have hE : ∀ (c : KB) (f : WK),
      (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)) (c ⊗ₜ[Ks] f)
        = c • R ((∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)) ((1 : L0) ⊗ₜ[Ks] f)) := by
    intro c f
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul, map_sum,
      hRs, hRt, map_one, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [mul_comm]
  rintro y ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c f =>
    rw [hE, map_smul, hRq, hq _ ⟨_, rfl⟩, map_zero, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

end GlobalTheory
