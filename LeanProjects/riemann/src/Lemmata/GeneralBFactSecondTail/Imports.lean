import Mathlib

universe u_1 u_2

namespace Bl.general_b_fact_second''''''

theorem goal1 :
  ∀ {K : Type u_1} [inst : Field.{u_1} K] [NumberField.{u_1} K] {V : Type u_2} [inst_2 : AddCommGroup.{u_2} V]
  [inst_3 : Module.{u_1, u_2} K V] [inst_4 : Module.{u_1, u_2} (NumberField.RingOfIntegers.{u_1} K) V]
  [IsScalarTower.{u_1, u_1, u_2} (NumberField.RingOfIntegers.{u_1} K) K V]
  (A : Submodule.{u_1, u_2} (NumberField.RingOfIntegers.{u_1} K) V) (x : V),
  Membership.mem.{u_2, u_2} (Submodule.span.{u_1, u_2} K (SetLike.coe.{u_2, u_2} A)) x →
    Exists.{u_1 + 1} fun (d : NumberField.RingOfIntegers.{u_1} K) ↦
      And (Ne.{u_1 + 1} d 0) (Membership.mem.{u_2, u_2} A (HSMul.hSMul.{u_1, u_2, u_2} d x)) := by
  intro K _ _ V _ _ _ _ A x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    have e1 : (d1 * d2) • y = d2 • (d1 • y) := by rw [mul_comm, mul_smul]
    have e2 : (d1 * d2) • z = d1 • (d2 • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact A.add_mem (A.smul_mem _ h1) (A.smul_mem _ h2)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨n, m⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    have hm : (m : NumberField.RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero m
    refine ⟨(m : NumberField.RingOfIntegers K) * d, mul_ne_zero hm hd, ?_⟩
    have key : algebraMap (NumberField.RingOfIntegers K) K ((m : NumberField.RingOfIntegers K) * d) * c
        = algebraMap (NumberField.RingOfIntegers K) K (n * d) := by
      rw [map_mul, map_mul]
      linear_combination (algebraMap (NumberField.RingOfIntegers K) K d) * hc
    have e : ((m : NumberField.RingOfIntegers K) * d) • (c • y) = n • (d • y) := by
      rw [← algebraMap_smul K ((m : NumberField.RingOfIntegers K) * d) (c • y), smul_smul, key,
        algebraMap_smul K, mul_smul]
    rw [e]
    exact A.smul_mem _ h

end Bl.general_b_fact_second''''''
