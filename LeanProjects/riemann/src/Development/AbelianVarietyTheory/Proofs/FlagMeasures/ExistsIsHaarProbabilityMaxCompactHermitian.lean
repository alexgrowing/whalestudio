import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem uh_mul {N : ℕ} {H A B : Matrix (Fin N) (Fin N) ℂ} (hA : Aᴴ * H * A = H) (hB : Bᴴ * H * B = H) :
    (A * B)ᴴ * H * (A * B) = H := by
  rw [Matrix.conjTranspose_mul]
  calc Bᴴ * Aᴴ * H * (A * B) = Bᴴ * (Aᴴ * H * A) * B := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hA, hB]

theorem uh_star {N : ℕ} {H A : Matrix (Fin N) (Fin N) ℂ} (hA : Aᴴ * H * A = H) (hu : A * Aᴴ = 1) :
    (Aᴴ)ᴴ * H * Aᴴ = H := by
  rw [Matrix.conjTranspose_conjTranspose]
  calc A * H * Aᴴ = A * (Aᴴ * H * A) * Aᴴ := by rw [hA]
    _ = (A * Aᴴ) * H * (A * Aᴴ) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hu, Matrix.one_mul, Matrix.mul_one]

def subKH (k r : ℕ) : Subgroup (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) where
  carrier := {u | (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ GlobalTheory.ThA.KH k r}
  mul_mem' := by
    intro a b ha hb
    exact ⟨uh_mul ha.1 hb.1, (a * b).2⟩
  one_mem' := by
    refine ⟨?_, (1 : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ).2⟩
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  inv_mem' := by
    intro a ha
    refine ⟨?_, a⁻¹.2⟩
    have hu : (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) *
        (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ = 1 := by
      have := Matrix.mem_unitaryGroup_iff.mp a.2
      rwa [Matrix.star_eq_conjTranspose] at this
    exact uh_star ha.1 hu

instance (k r : ℕ) : MeasurableSpace (subKH k r) := borel _
instance (k r : ℕ) : BorelSpace (subKH k r) := ⟨rfl⟩

instance (k r : ℕ) : CompactSpace (subKH k r) := by
  have hc : IsClosed ((subKH k r : Set (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ))) := by
    have : ((subKH k r : Set (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ))) =
        (Subtype.val : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ → _) ⁻¹' GlobalTheory.ThA.KH k r := rfl
    rw [this]
    exact (isCompact_KH k r).isClosed.preimage continuous_subtype_val
  exact isCompact_iff_compactSpace.mp hc.isCompact

def incKH (k r : ℕ) (u : subKH k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  ((u : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) : Matrix _ _ ℂ)

theorem continuous_incKH (k r : ℕ) : Continuous (incKH k r) :=
  continuous_subtype_val.comp continuous_subtype_val

theorem incKH_mem (k r : ℕ) (u : subKH k r) : incKH k r u ∈ GlobalTheory.ThA.KH k r := u.2

theorem exists_isHaarKH : ∀ k r : ℕ, ∃ μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    GlobalTheory.KFinAvg.IsHaarKH k r μ := by
  intro k r
  let ν : Measure (subKH k r) := Measure.haarMeasure ⊤
  have hmeas : Measurable (incKH k r) := (continuous_incKH k r).measurable
  have hν : IsProbabilityMeasure ν := ⟨by
    have := Measure.haarMeasure_self (G := subKH k r) (K₀ := ⊤)
    simpa using this⟩
  have hKm : MeasurableSet (GlobalTheory.ThA.KH k r) := (isCompact_KH k r).isClosed.measurableSet
  refine ⟨ν.map (incKH k r), ?_, ?_, ?_, ?_⟩
  · exact Measure.isProbabilityMeasure_map hmeas.aemeasurable
  · rw [Measure.map_apply hmeas hKm.compl]
    have : incKH k r ⁻¹' (GlobalTheory.ThA.KH k r)ᶜ = ∅ := by
      ext u
      simp [incKH_mem k r u]
    rw [this, measure_empty]
  · intro a ha
    let au : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := ⟨a, ha.2⟩
    let a' : subKH k r := ⟨au, ha⟩
    have h := map_mul_left_eq_self ν a'
    rw [Measure.map_map (measurable_const_mul a) hmeas]
    conv_rhs => rw [← h]
    rw [Measure.map_map hmeas (measurable_const_mul _)]
    rfl
  · intro U hU h1
    rw [Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage (continuous_incKH k r)).measure_pos ν ⟨1, h1⟩

end GlobalTheory.KFinAvg
