import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace VeroneseArith

open Veronese

def sq (D : ℕ) (i : Fin (D + 1)) : Ix (Idx D) := ⟨(), ⟨(i, i), le_rfl⟩⟩

theorem sq_injective (D : ℕ) : Function.Injective (sq D) := by
  intro i j h
  have := congrArg (fun q : Ix (Idx D) => q.2.1.1) h
  simpa [sq] using this

theorem t_ne_zero (D : ℕ) (i : Fin (D + 1)) : t D i ≠ 0 := by
  rw [t, ← map_zero (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D))]
  exact (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).ne (X_ne_zero i)

theorem aeval_sq (D : ℕ) (f : MvPolynomial (Fin (D + 1)) ℤ) :
    aeval (x D ∘ sq D) f = algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)
      (MvPolynomial.map (Int.castRingHom ℚ) (expand 2 f)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, hp, map_mul, map_mul, map_mul, aeval_X, expand_X, map_pow, map_X, map_pow]
    simp [x, sq, t, pow_two]

theorem coordIdeal_sq (D : ℕ) : coordIdeal ℤ (x D ∘ sq D) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot, ← sum_homogeneousComponent f]
  refine Finset.sum_eq_zero fun d _ => ?_
  have h1 : aeval (x D ∘ sq D) (homogeneousComponent d f) = 0 := by
    rw [← coeff_coneMap ℤ]
    rw [coordIdeal, RingHom.mem_ker] at hf
    rw [hf, Polynomial.coeff_zero]
  rw [aeval_sq] at h1
  have h2 := IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) (h1.trans (map_zero _).symm)
  have h3 := MvPolynomial.map_injective _ (Int.castRingHom ℚ).injective_int (h2.trans (map_zero _).symm)
  exact (expand_eq_zero two_pos).mp h3

theorem isIntegral_coord (D : ℕ) (q : Ix (Idx D)) :
    IsIntegral (coneRing ℤ (x D ∘ sq D)) (Polynomial.C (x D q) * Polynomial.X : Polynomial (Fld D)) := by
  have hmem : ∀ i, (Polynomial.C (x D (sq D i)) * Polynomial.X : Polynomial (Fld D)) ∈
      coneRing ℤ (x D ∘ sq D) := fun i => ⟨X i, by simp [coneMap]⟩
  have hsq : (Polynomial.C (x D q) * Polynomial.X : Polynomial (Fld D)) ^ 2 =
      (Polynomial.C (x D (sq D q.2.1.1)) * Polynomial.X) * (Polynomial.C (x D (sq D q.2.1.2)) * Polynomial.X) := by
    simp only [x, sq, map_mul]
    ring
  refine IsIntegral.of_pow two_pos ?_
  rw [hsq]
  exact isIntegral_algebraMap (R := coneRing ℤ (x D ∘ sq D)) (A := Polynomial (Fld D))
    (x := ⟨_, mul_mem (hmem _) (hmem _)⟩)

theorem isProjFrame_sq (D : ℕ) : IsProjFrame (x D) (sq D) :=
  ⟨sq_injective D, coordIdeal_sq D, isIntegral_coord D⟩

theorem proof : VeroneseArith.Statement := by
  intro D _
  refine ⟨⟨()⟩, ⟨coordIdeal_isPrime ℤ _, isMultiHomogIdeal_coordIdeal _, ?_⟩, isHorizontal_coordIdeal _, ?_⟩
  · intro k
    refine ⟨⟨(0, 0), le_rfl⟩, ?_⟩
    rw [X_mem_coordIdeal_iff]
    exact mul_ne_zero (t_ne_zero D 0) (t_ne_zero D 0)
  · rw [ringKrullDim_quot_of_frame _ (sq D) (isProjFrame_sq D), Fintype.card_unit]

end VeroneseArith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
