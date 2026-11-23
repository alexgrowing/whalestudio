import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem covol_prod_le_tsum_slices : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂] [MeasurableMul G₂] (μ₁ : Measure G₁) (μ₂ : Measure G₂) [SigmaFinite μ₁] [SigmaFinite μ₂] [μ₂.IsMulLeftInvariant] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (A : Set (G₁ × G₂)) (ι : Type) [Countable ι] (x : ι → G₂) (Γc Ac : ι → Set G₁), MeasurableSet (K : Set G₂) → (∀ c, ∀ g ∈ Γc c, ∃ γ ∈ Γ, γ.1 = g ∧ (x c)⁻¹ * γ.2 * x c ∈ K) → (∀ y ∈ A, ∃ c, ∃ γ ∈ Γ, ∃ k ∈ K, γ.2 * y.2 = x c * k ∧ γ.1 * y.1 ∈ Ac c) → μ₂ K ≠ ⊤ → covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤ μ₂ K * ∑' c, covol (Γc c) μ₁ (Ac c) := by
  intro G₁ G₂ _ _ _ _ _ μ₁ μ₂ _ _ _ Γ K A ι _ x Γc Ac hK hΓ hA hfin
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hb => ?_
  obtain ⟨ε', hε', hsum⟩ := ENNReal.exists_pos_sum_of_countable (ε := (ε : ENNReal))
    (by exact_mod_cast hε.ne') ι
  have key : ∀ c, ∃ D : Set G₁, MeasurableSet D ∧
      μ₂ K * μ₁ D ≤ μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c ∧
      (D = Set.univ ∨ ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D) := by
    intro c
    by_cases h0 : μ₂ K = 0
    · exact ⟨Set.univ, MeasurableSet.univ, by simp [h0], Or.inl rfl⟩
    · have hc : μ₂ K * covol (Γc c) μ₁ (Ac c) ≠ ⊤ :=
        ne_top_of_le_ne_top hb.ne (mul_le_mul_right (ENNReal.le_tsum c) _)
      have hlt : μ₂ K * covol (Γc c) μ₁ (Ac c) < μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c :=
        ENNReal.lt_add_right hc (by exact_mod_cast (hε' c).ne')
      have h2 : μ₂ K * covol (Γc c) μ₁ (Ac c) = ⨅ (D : Set G₁) (_ : MeasurableSet D)
          (_ : ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D), μ₂ K * μ₁ D := by
        simp only [covol, ENNReal.mul_iInf_of_ne h0 hfin]
      rw [h2] at hlt
      simp only [iInf_lt_iff] at hlt
      obtain ⟨D, hD, hcov, hlt⟩ := hlt
      rw [← h2] at hlt
      exact ⟨D, hD, hlt.le, Or.inr hcov⟩
  choose D hDm hDle hDcov using key
  have hKm : ∀ c, MeasurableSet ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)) := fun c =>
    measurable_const_mul _ hK
  have h1 : covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤
      (μ₁.prod μ₂) (⋃ c, D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂))) := by
    refine iInf_le_of_le _ (iInf_le_of_le (MeasurableSet.iUnion fun c => (hDm c).prod (hKm c))
      (iInf_le_of_le ?_ le_rfl))
    intro y hy
    obtain ⟨c, γ, hγ, k, hk, h2, h1⟩ := hA y hy
    rcases hDcov c with hu | hcov
    · refine ⟨γ, hγ, Set.mem_iUnion.2 ⟨c, by simp [hu], ?_⟩⟩
      simpa [h2] using hk
    · obtain ⟨g, hg, hgD⟩ := hcov _ h1
      obtain ⟨δ, hδ, rfl, hδK⟩ := hΓ c g hg
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, Set.mem_iUnion.2 ⟨c, by simpa [mul_assoc] using hgD, ?_⟩⟩
      have := K.mul_mem hδK hk
      simpa [mul_assoc, h2] using this
  refine h1.trans ((measure_iUnion_le _).trans ?_)
  calc ∑' c, (μ₁.prod μ₂) (D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)))
      ≤ ∑' c, (μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c) := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        rw [Measure.prod_prod, measure_preimage_mul, mul_comm]
        exact hDle c
    _ ≤ _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        exact add_le_add le_rfl hsum.le

end GlobalTheory.FlagMeas
