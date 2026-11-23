import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecRankSpecialize.Statement : Prop :=
  ∀ (R K κ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field κ] [Algebra R κ] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Vertical.Par e n → R),
    Function.Surjective (algebraMap R κ) → Module.Finite R (Vertical.SecAlg Q y) →
      Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) ≤
        Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))

theorem SecRankSpecialize.hypotheses_inhabited :
    letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra
    IsDomain (PowerSeries ℚ) ∧ IsLocalRing (PowerSeries ℚ) ∧
      IsFractionRing (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) ∧
      Function.Surjective (algebraMap (PowerSeries ℚ) ℚ) ∧
      Module.Finite (PowerSeries ℚ)
        (Vertical.SecAlg (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ)))
          (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))) := by
  letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra
  refine ⟨inferInstance, inferInstance, inferInstance,
    fun a => ⟨PowerSeries.C a, by simp [RingHom.algebraMap_toAlgebra]⟩, ?_⟩
  set I := Vertical.secIdeal (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ)))
    (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))
  have hX : ∀ j : Fin 1, Ideal.Quotient.mk I (X j) = 1 := by
    intro j
    rw [Fin.fin_one_eq_zero j, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_sup_right (Ideal.subset_span ?_)
    simp [Vertical.chartForm, linForm]
  have hrange : ∀ p : MvPolynomial (Fin 1) (PowerSeries ℚ),
      Ideal.Quotient.mk I p ∈ Set.range (algebraMap (PowerSeries ℚ) (Vertical.SecAlg ⊥
        (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ)))) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | mul_X p j hp =>
      obtain ⟨a, ha⟩ := hp
      exact ⟨a, by rw [map_mul, hX, mul_one, ha]⟩
  refine Module.Finite.of_surjective (Algebra.linearMap (PowerSeries ℚ) _) ?_
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hrange p

end

end GroundTheory.Heights₂.Heights
