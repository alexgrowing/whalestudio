import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineBis
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

namespace FlagGenericPointValue

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem isValueAt_zero (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt y 0 z 0 := by
  simpa using isValueAt_intCast y z 0

theorem isValueAt_sum {α : Type*} (s : Finset α) {f : α → Ω} {g : α → ℂ}
    (h : ∀ a ∈ s, IsValueAt y (f a) z (g a)) : IsValueAt y (∑ a ∈ s, f a) z (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_zero y z
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact isValueAt_add (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

variable {σ : Type}

theorem valPoly_X (s : σ) : ValPoly y z (X s : MvPolynomial σ Ω) (X s) := by
  classical
  intro μ
  rw [coeff_X, coeff_X]
  split_ifs
  · simpa using isValueAt_intCast y z 1
  · exact isValueAt_zero y z

theorem valPoly_C {a : Ω} {v : ℂ} (h : IsValueAt y a z v) :
    ValPoly y z (C a : MvPolynomial σ Ω) (C v) := by
  classical
  intro μ
  rw [coeff_C, coeff_C]
  split_ifs
  · exact h
  · exact isValueAt_zero y z

omit [Fintype K] in

theorem valPoly_add {A A' : MvPolynomial σ Ω} {B B' : MvPolynomial σ ℂ} (h : ValPoly y z A B)
    (h' : ValPoly y z A' B') : ValPoly y z (A + A') (B + B') := fun μ => by
  rw [coeff_add, coeff_add]
  exact isValueAt_add (h μ) (h' μ)

theorem valPoly_mul {A A' : MvPolynomial σ Ω} {B B' : MvPolynomial σ ℂ} (h : ValPoly y z A B)
    (h' : ValPoly y z A' B') : ValPoly y z (A * A') (B * B') := fun μ => by
  classical
  rw [coeff_mul, coeff_mul]
  exact isValueAt_sum _ fun p _ => isValueAt_mul (h p.1) (h' p.2)

theorem valPoly_one : ValPoly y z (1 : MvPolynomial σ Ω) 1 := by
  simpa using valPoly_C (σ := σ) (isValueAt_intCast y z 1)

theorem valPoly_zero : ValPoly y z (0 : MvPolynomial σ Ω) 0 := fun μ => by
  simpa using isValueAt_zero y z

theorem valPoly_sum {α : Type*} (s : Finset α) {A : α → MvPolynomial σ Ω} {B : α → MvPolynomial σ ℂ}
    (h : ∀ a ∈ s, ValPoly y z (A a) (B a)) : ValPoly y z (∑ a ∈ s, A a) (∑ a ∈ s, B a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valPoly_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact valPoly_add (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem valPoly_prod {α : Type*} (s : Finset α) {A : α → MvPolynomial σ Ω} {B : α → MvPolynomial σ ℂ}
    (h : ∀ a ∈ s, ValPoly y z (A a) (B a)) : ValPoly y z (∏ a ∈ s, A a) (∏ a ∈ s, B a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valPoly_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact valPoly_mul (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem proof : FlagGenericPointValue.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl z x x' V V' hx hV j
  obtain ⟨k | q, t⟩ := j
  · exact valPoly_mul (valPoly_X _) (valPoly_C (hx _))
  · exact valPoly_mul (valPoly_X _) (valPoly_sum _ fun c _ =>
      valPoly_mul (valPoly_prod _ fun a _ => valPoly_X _) (valPoly_C (hV q t c)))

end FlagGenericPointValue

end GroundTheory.Heights₂.Heights.LowerBoundFree
