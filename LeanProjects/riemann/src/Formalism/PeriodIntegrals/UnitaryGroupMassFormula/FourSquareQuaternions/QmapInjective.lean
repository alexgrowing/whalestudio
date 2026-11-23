import Mathlib
import Formalism.PeriodIntegrals.KerIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.FourSqOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.QuatMatTransposeMul

noncomputable section
open scoped BigOperators Matrix

namespace PI.KerIso.FourSqW

open PI.KerFourSqW

def qmap {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) :
    (Fin 4 → E) →ₗ[K] (Fin 4 × n → K) where
  toFun x w := ∑ a, (Q w.2 w.1 a : K) * b.repr (x a) w.2
  map_add' x y := by
    ext w
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext w
    simp [Finset.mul_sum, mul_left_comm]

theorem qmap_apply {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → E) (w : Fin 4 × n) :
    qmap b Q x w = ∑ a, (Q w.2 w.1 a : K) * b.repr (x a) w.2 := rfl

theorem qmap_back {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (q : n → ℚ)
    (hQ : ∀ i, (Q i)ᵀ * Q i = q i • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (x : Fin 4 → E) (a' : Fin 4) (i : n) :
    ∑ c, (Q i c a' : K) * qmap b Q x (c, i) = (q i : K) * b.repr (x a') i := by
  simp only [qmap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ a, ∑ c, (Q i c a' : K) * ((Q i c a : K) * b.repr (x a) i)
      = (∑ c, (Q i c a' : K) * (Q i c a : K)) * b.repr (x a) i := by
    intro a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  simp_rw [h, sum_mul_cast (Q i) (q i) (hQ i), ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem qmap_injective {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (q : n → ℚ) (hq : ∀ i, 0 < q i)
    (hQ : ∀ i, (Q i)ᵀ * Q i = q i • (1 : Matrix (Fin 4) (Fin 4) ℚ)) :
    Function.Injective (qmap b Q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  funext a'
  rw [b.ext_elem_iff]
  intro i
  have h := qmap_back b Q q hQ x a' i
  simp only [hx, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  have hqi : (q i : K) ≠ 0 := by exact_mod_cast (hq i).ne'
  have h0 : b.repr (x a') i = 0 := by
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact absurd h1 hqi
    · exact h1
  simp [h0]

theorem from_diagonal : FromDiag := by
  intro K E _ _ _ _ _ cj n _ b q hq hb
  choose Q hQ using fun i => exists_quat (q i) (hq i)
  have : Module.Finite K E := Module.Finite.of_basis b
  have hdim : Module.finrank K (Fin 4 → E) = Module.finrank K (Fin 4 × n → K) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis b,
      Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  refine ⟨(qmap b Q).linearEquivOfInjective (qmap_injective b Q q hq hQ) hdim, ?_⟩
  intro x y
  simp only [LinearMap.linearEquivOfInjective_apply]
  rw [map_sum]
  unfold DiagId at hb
  simp_rw [hb]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_comm (γ := Fin 4)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : ∀ c, algebraMap K E (qmap b Q x (c, i))
      = ∑ a, (Q i c a : E) * algebraMap K E (b.repr (x a) i) := by
    intro c
    rw [qmap_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_ratCast]
  have hy : ∀ c, algebraMap K E (qmap b Q y (c, i))
      = ∑ a, (Q i c a : E) * algebraMap K E (b.repr (y a) i) := by
    intro c
    rw [qmap_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_ratCast]
  simp_rw [hx, hy]
  rw [quat_herm cj (Q i) (q i) (hQ i), Finset.mul_sum]

end PI.KerIso.FourSqW
