import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem exists_quot_of_mem_rayP {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K))
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hI : I ∈ rayP 𝔮) :
    ∃ a b : 𝓞 K, a - 1 ∈ 𝔮 ∧ b - 1 ∈ 𝔮 ∧ b ≠ 0 ∧
      (I : FractionalIdeal (𝓞 K)⁰ K) * ((Ideal.span {b} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hmul : ∀ x y : 𝓞 K, x - 1 ∈ 𝔮 → y - 1 ∈ 𝔮 → x * y - 1 ∈ 𝔮 := by
    intro x y hx hy
    have : x * y - 1 = (x - 1) * y + (y - 1) := by ring
    rw [this]
    exact 𝔮.add_mem (𝔮.mul_mem_right _ hx) hy
  unfold rayP at hI
  induction hI using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hx⟩ := hx
    refine ⟨a, 1, ha, by simp, one_ne_zero, ?_⟩
    rw [hx]; simp
  | one => exact ⟨1, 1, by simp, by simp, one_ne_zero, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, ha, hb, hb0, h⟩ := hx
    obtain ⟨c, d, hc, hd, hd0, h'⟩ := hy
    refine ⟨a * c, b * d, hmul _ _ ha hc, hmul _ _ hb hd, mul_ne_zero hb0 hd0, ?_⟩
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, ← h, ← h', Units.val_mul]
    ring
  | inv x _ hx =>
    obtain ⟨a, b, ha, hb, hb0, h⟩ := hx
    refine ⟨b, a, hb, ha, ?_, ?_⟩
    · rintro rfl
      have h0 : ((Ideal.span {b} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
        rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
        exact hb0
      have h1 := mul_ne_zero x.ne_zero h0
      rw [h] at h1
      apply h1
      rw [FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
    · rw [← h, ← mul_assoc, Units.inv_mul, one_mul]

theorem exists_generator_of_mem_rayPrimes :
    ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → ∀ (X : ℝ),
      ∀ v ∈ rayPrimes 𝔮 X, ∃ π : 𝓞 K, v.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  intro K _ _ 𝔮 _ X v hv
  obtain ⟨-, -, I, hI, hIv⟩ := hv
  obtain ⟨a, b, ha, hb, hb0, h⟩ := exists_quot_of_mem_rayP 𝔮 hI
  rw [hIv, ← FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_inj] at h
  have hmem : a ∈ Ideal.span {b} := by
    have h1 : Ideal.span {a} ≤ Ideal.span {b} := by
      rw [← h]; first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
    exact h1 (Ideal.mem_span_singleton_self a)
  obtain ⟨π, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨π, ?_, ?_⟩
  · rw [← Ideal.span_singleton_mul_span_singleton] at h
    have h0 : (Ideal.span {b} : Ideal (𝓞 K)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
    exact mul_right_cancel₀ h0 h
  · have : π - 1 = (π * b - 1) - π * (b - 1) := by ring
    rw [this]
    exact 𝔮.sub_mem ha (𝔮.mul_mem_left _ hb)

end GlobalTheory.Mem.An
