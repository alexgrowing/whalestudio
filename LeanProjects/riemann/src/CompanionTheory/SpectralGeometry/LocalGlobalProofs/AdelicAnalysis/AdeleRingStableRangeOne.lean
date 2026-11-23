import Mathlib

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdeleStableRange

theorem local_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (a b x y : K) (h : x * a + y * b = 1) :
    ∃ t : K, (t = 0 ∨ t = 1) ∧ a + t * b ≠ 0 ∧
      (w a ≤ 1 → w b ≤ 1 → w x ≤ 1 → w y ≤ 1 → w (a + t * b) = 1) := by
  have hb0 : a = 0 → b ≠ 0 := by
    rintro rfl rfl
    simp at h
  by_cases hint : w a ≤ 1 ∧ w b ≤ 1 ∧ w x ≤ 1 ∧ w y ≤ 1
  · obtain ⟨ha, hb, hx, hy⟩ := hint
    by_cases ha1 : w a = 1
    · refine ⟨0, Or.inl rfl, ?_, ?_⟩
      · intro h0
        have : a = 0 := by simpa using h0
        rw [this, map_zero] at ha1
        exact zero_ne_one ha1
      · intro _ _ _ _
        simpa using ha1
    · have hlt : w a < 1 := lt_of_le_of_ne ha ha1
      have hxa : w (x * a) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) hlt
      have hyb : w (y * b) = 1 := by
        have h1 : y * b = 1 + (-(x * a)) := by linear_combination h
        rw [h1, Valuation.map_add_eq_of_lt_left w (by rw [Valuation.map_neg, map_one]; exact hxa),
          map_one]
      have hb1 : w b = 1 := by
        refine le_antisymm hb ?_
        rw [map_mul] at hyb
        rw [← hyb]
        exact mul_le_of_le_one_left' hy
      have hab : w (a + 1 * b) = 1 := by
        rw [one_mul, Valuation.map_add_eq_of_lt_right w (by rw [hb1]; exact hlt), hb1]
      refine ⟨1, Or.inr rfl, ?_, fun _ _ _ _ => hab⟩
      intro h0
      rw [h0, map_zero] at hab
      exact zero_ne_one hab
  · by_cases ha0 : a = 0
    · refine ⟨1, Or.inr rfl, ?_, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hint⟩
      simpa [ha0] using hb0 ha0
    · refine ⟨0, Or.inl rfl, by simpa using ha0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hint⟩

theorem local_field {K : Type*} [Field K] (a b x y : K) (h : x * a + y * b = 1) :
    ∃ t : K, IsUnit (a + t * b) := by
  by_cases ha : a = 0
  · refine ⟨1, ?_⟩
    rw [isUnit_iff_ne_zero, ha]
    rintro h0
    have hb : b = 0 := by simpa using h0
    simp [ha, hb] at h
  · exact ⟨0, by simpa [isUnit_iff_ne_zero] using ha⟩

theorem finite_part (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (a b : FiniteAdeleRing R K) (hab : IsCoprime a b) :
    ∃ t : FiniteAdeleRing R K, IsUnit (a + t * b) := by
  obtain ⟨x, y, hxy⟩ := hab
  have hloc : ∀ v : HeightOneSpectrum R, x v * a v + y v * b v = 1 := fun v =>
    congrArg (fun z : FiniteAdeleRing R K => z v) hxy
  choose e he hne hval using fun v : HeightOneSpectrum R =>
    local_val (Valued.v : Valuation (v.adicCompletion K) _) (a v) (b v) (x v) (y v) (hloc v)
  have hint : ∀ v : HeightOneSpectrum R, e v ∈ v.adicCompletionIntegers K := by
    intro v
    rcases he v with h | h <;> rw [h]
    · exact zero_mem _
    · exact one_mem _
  let E : FiniteAdeleRing R K := ⟨e, Filter.Eventually.of_forall hint⟩
  refine ⟨E, ?_⟩
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun v h0 => hne v h0, ?_⟩
  filter_upwards [a.2, b.2, x.2, y.2] with v h1 h2 h3 h4
  exact hval v h1 h2 h3 h4

theorem infinite_part (K : Type*) [Field K] [NumberField K] (a b : InfiniteAdeleRing K)
    (hab : IsCoprime a b) : ∃ t : InfiniteAdeleRing K, IsUnit (a + t * b) := by
  obtain ⟨x, y, hxy⟩ := hab
  have hloc : ∀ v : InfinitePlace K, x v * a v + y v * b v = 1 := fun v =>
    congrArg (fun z : InfiniteAdeleRing K => z v) hxy
  choose t ht using fun v : InfinitePlace K => local_field (a v) (b v) (x v) (y v) (hloc v)
  exact ⟨t, Pi.isUnit_iff.2 ht⟩

theorem adeleRing_stableRange_one : ∀ (F : Type) [Field F] [NumberField F] (a b : AdeleRing (𝓞 F) F),
    IsCoprime a b → ∃ t, IsUnit (a + t * b) := by
  intro F _ _ a b hab
  obtain ⟨x, y, hxy⟩ := hab
  obtain ⟨t₁, u₁⟩ := infinite_part F a.1 b.1 ⟨x.1, y.1, congrArg Prod.fst hxy⟩
  obtain ⟨t₂, u₂⟩ := finite_part (𝓞 F) F a.2 b.2 ⟨x.2, y.2, congrArg Prod.snd hxy⟩
  exact ⟨(t₁, t₂), Prod.isUnit_iff.2 ⟨u₁, u₂⟩⟩

end GlobalTheory.CompanionTheory.AdeleStableRange
