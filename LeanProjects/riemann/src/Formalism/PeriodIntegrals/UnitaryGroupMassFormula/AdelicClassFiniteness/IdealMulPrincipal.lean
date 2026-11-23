import Mathlib

noncomputable section

namespace PIW.AdelClassFin

open NumberField
open scoped nonZeroDivisors

theorem ideal_mul_principal {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI0 : I ∈ (Ideal (𝓞 E))⁰)
    (A : (Ideal (𝓞 E))⁰) (hA : ClassGroup.mk0 A = (ClassGroup.mk0 (⟨I, hI0⟩ : (Ideal (𝓞 E))⁰))⁻¹) :
    ∃ c : 𝓞 E, I * (A : Ideal (𝓞 E)) = Ideal.span {c} := by
  have h1 : ClassGroup.mk0 ((⟨I, hI0⟩ : (Ideal (𝓞 E))⁰) * A) = 1 := by
    rw [map_mul, hA, mul_inv_cancel]
  obtain ⟨c, hc⟩ := ((ClassGroup.mk0_eq_one_iff (((⟨I, hI0⟩ : (Ideal (𝓞 E))⁰) * A).2)).mp h1).principal
  exact ⟨c, hc⟩

def IdealBoundAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], ∃ B : ℕ, ∀ I : Ideal (𝓞 E), I ≠ ⊥ → ∃ c ∈ I, c ≠ 0 ∧ ∃ e : ℕ,
    1 ≤ e ∧ e ≤ B ∧ ∀ g ∈ I, ∃ q : 𝓞 E, (e : 𝓞 E) * g = c * q

theorem star_fixed_reps (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) :
    ∃ R : Set E, R.Finite ∧ (N ≠ 0 → ∀ β : 𝓞 E, star (algebraMap (𝓞 E) E β) = algebraMap (𝓞 E) E β →
      ∃ r ∈ R, ∃ s : 𝓞 E, algebraMap (𝓞 E) E β = r + N * algebraMap (𝓞 E) E s ∧
        star (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s) := by
  classical
  by_cases hN : N = 0
  · exact ⟨∅, Set.finite_empty, fun h => absurd hN h⟩
  let I : Ideal (𝓞 E) := Ideal.span {(N : 𝓞 E)}
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let P : 𝓞 E → Prop := fun β => star (algebraMap (𝓞 E) E β) = algebraMap (𝓞 E) E β
  let pick : 𝓞 E ⧸ I → E := fun q =>
    if h : ∃ β, P β ∧ Ideal.Quotient.mk I β = q then algebraMap (𝓞 E) E h.choose else 0
  refine ⟨Set.range pick, Set.finite_range pick, fun _ β hβ => ?_⟩
  have h : ∃ b, P b ∧ Ideal.Quotient.mk I b = Ideal.Quotient.mk I β := ⟨β, hβ, rfl⟩
  obtain ⟨hP, hq⟩ := h.choose_spec
  have hP' : star (algebraMap (𝓞 E) E h.choose) = algebraMap (𝓞 E) E h.choose := hP
  have hpick : pick (Ideal.Quotient.mk I β) = algebraMap (𝓞 E) E h.choose := by
    simp only [pick, dif_pos h]
  have hmem : β - h.choose ∈ I := Ideal.Quotient.eq.mp hq.symm
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
  have e1 := congrArg (algebraMap (𝓞 E) E) hs
  rw [map_mul, map_sub, map_natCast] at e1
  refine ⟨pick (Ideal.Quotient.mk I β), ⟨_, rfl⟩, s, ?_, ?_⟩
  · rw [hpick]
    linear_combination (-1 : E) * e1
  · have e2 := congrArg star e1
    rw [star_mul', star_natCast, star_sub, hβ, hP', ← e1] at e2
    exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr hN) e2

end PIW.AdelClassFin
