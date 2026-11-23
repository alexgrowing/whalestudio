import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineMore
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

namespace FlagPolynomialValue

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isValueAt_zero (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt y (0 : Ω) z (0 : ℂ) := by
  simpa using isValueAt_intCast y z 0

theorem isValueAt_sum {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {α : Type} (s : Finset α) (f : α → Ω)
    (g : α → ℂ) (h : ∀ a ∈ s, IsValueAt y (f a) z (g a)) :
    IsValueAt y (∑ a ∈ s, f a) z (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_zero y z
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact isValueAt_add (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

omit [Fintype K] in

theorem valPoly_add {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {σ : Type} {P P' : MvPolynomial σ Ω}
    {Q Q' : MvPolynomial σ ℂ} (h : ValPoly y z P Q) (h' : ValPoly y z P' Q') :
    ValPoly y z (P + P') (Q + Q') := fun μ => by
  rw [coeff_add, coeff_add]; exact isValueAt_add (h μ) (h' μ)

theorem valPoly_mul {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {σ : Type} {P P' : MvPolynomial σ Ω}
    {Q Q' : MvPolynomial σ ℂ} (h : ValPoly y z P Q) (h' : ValPoly y z P' Q') :
    ValPoly y z (P * P') (Q * Q') := fun μ => by
  classical
  rw [coeff_mul, coeff_mul]
  exact isValueAt_sum _ _ _ fun x _ => isValueAt_mul (h x.1) (h' x.2)

theorem valPoly_intC (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) {σ : Type} (n : ℤ) :
    ValPoly y z (C (n : Ω) : MvPolynomial σ Ω) (C (n : ℂ)) := fun μ => by
  classical
  rw [coeff_C, coeff_C]
  split_ifs
  · exact isValueAt_intCast y z n
  · exact isValueAt_zero y z

theorem proof : FlagPolynomialValue.Statement := by
  intro K _ ι _ Ω _ y z σ κ A B hAB F
  induction F using MvPolynomial.induction_on with
  | C n =>
    have h := valPoly_intC y z (σ := σ) n
    simp only [aeval_C, map_intCast] at h ⊢
    simpa using h
  | add p q hp hq =>
    rw [map_add, map_add]; exact valPoly_add hp hq
  | mul_X p j hp =>
    rw [map_mul, map_mul, aeval_X, aeval_X]; exact valPoly_mul hp (hAB j)

end FlagPolynomialValue

end GroundTheory.Heights₂.Heights.LowerBoundFree
