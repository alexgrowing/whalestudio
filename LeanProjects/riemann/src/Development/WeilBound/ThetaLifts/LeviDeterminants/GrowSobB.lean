import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

theorem exists_reps (m : ℕ) (hm : 1 ≤ m) :
    ∃ rep : (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin m) → FiniteAdeleRing (𝓞 F) F,
      ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ v, y v ∈ v.adicCompletionIntegers F) →
        ∃ r, ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = rep r + m • a := by
  let b := RingOfIntegers.basis F
  let φ : 𝓞 F →+* FiniteAdeleRing (𝓞 F) F := (algebraMap F _).comp (algebraMap (𝓞 F) F)
  refine ⟨fun r => φ (∑ j, ((r j : ℕ) : ℤ) • b j), fun y hy => ?_⟩
  obtain ⟨x, a, ha, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F m hm).2 y hy
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have h0 : ∀ j, 0 ≤ b.repr x j % m := fun j => Int.emod_nonneg _ hm'.ne'
  refine ⟨fun j => ⟨(b.repr x j % m).toNat, ?_⟩, φ (∑ j, (b.repr x j / m) • b j) + a, fun v => ?_, ?_⟩
  · have := Int.emod_lt_of_pos (b.repr x j) hm'
    have := h0 j
    omega
  · exact add_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v _) (ha v)
  · rw [h, nsmul_add, ← add_assoc, ← map_nsmul, ← map_add]
    congr 1
    change φ x = _
    congr 1
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.toNat_of_nonneg (h0 j), ← natCast_zsmul, smul_smul, ← add_smul, Int.emod_add_mul_ediv]

def Om : Set (κ → FiniteAdeleRing (𝓞 F) F) := {y | ∀ i v, y i v ∈ v.adicCompletionIntegers F}

theorem measure_Om_le [MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F)] [BorelSpace (κ → FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (κ → FiniteAdeleRing (𝓞 F) F)) [ν.IsAddRightInvariant] :
    ∃ k : ℕ, ∀ m : ℕ, 1 ≤ m → ν (Om F κ) ≤ (m : ℝ≥0∞) ^ k * ν ((fun u => m • u) '' Om F κ) := by
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) * Fintype.card κ, fun m hm => ?_⟩
  obtain ⟨rep, h⟩ := exists_reps F m hm
  have hsub : Om F κ ⊆ ⋃ r : κ → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin m,
      (fun y => y + -fun i => rep (r i)) ⁻¹' ((fun u => m • u) '' Om F κ) := fun y hy => by
    choose r a ha e using fun i => h (y i) (hy i)
    refine Set.mem_iUnion.2 ⟨r, a, ha, funext fun i => ?_⟩
    change m • a i = y i + -rep (r i)
    rw [e i]
    abel
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans (le_of_eq ?_))
  simp only [measure_preimage_add_right, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, pow_mul]

end PositivityTheory.ThKF0.Grow
