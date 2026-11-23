import Mathlib

open MeasureTheory

theorem UpperTheory.ConvolutionTheory.K.intEst :
    ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (h : X → ℝ) (k c o : X → ℂ) (Z A B : ℝ),
      Measurable h → Integrable c ν → AEStronglyMeasurable o ν → 0 ≤ A → 0 ≤ B → (∀ x, k x = c x + o x) → (∀ x, Z < h x → k x = 0) →
      (∀ x, h x ≤ Z → ‖o x‖ ≤ A) → (∀ x, Z < h x → ‖c x‖ ≤ B) →
      ‖∫ x, k x ∂ν - ∫ x, c x ∂ν‖ ≤ ν.real Set.univ * A + ν.real Set.univ * B := by
  intro X _ ν _ h k c o Z A B hh hc ho hA hB hk h0 hoA hcB
  set S : Set X := {x | h x ≤ Z}
  have hS : MeasurableSet S := measurableSet_le hh measurable_const
  have e1 : ∀ x, k x - c x = S.indicator o x - Sᶜ.indicator c x := by
    intro x
    by_cases hx : x ∈ S
    · simp [hx, hk x]
    · simp [hx, h0 x (not_le.1 hx)]
  have b1 : ∀ x, ‖S.indicator o x‖ ≤ A := fun x => by
    by_cases hx : x ∈ S
    · simpa [hx] using hoA x hx
    · simpa [hx] using hA
  have b2 : ∀ x, ‖Sᶜ.indicator c x‖ ≤ B := fun x => by
    by_cases hx : x ∈ S
    · simpa [hx] using hB
    · simpa [hx] using hcB x (not_le.1 hx)
  have i1 : Integrable (S.indicator o) ν := Integrable.of_bound (ho.indicator hS) A (Filter.Eventually.of_forall b1)
  have i2 : Integrable (Sᶜ.indicator c) ν := hc.indicator hS.compl
  have ik : Integrable k ν := by
    have : k = fun x => (S.indicator o x - Sᶜ.indicator c x) + c x := funext fun x => by rw [← e1]; ring
    rw [this]
    exact (i1.sub i2).add hc
  rw [← integral_sub ik hc]
  simp_rw [e1]
  rw [integral_sub i1 i2]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [mul_comm]; exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall b1)
  · rw [mul_comm]; exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall b2)
