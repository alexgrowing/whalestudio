import Mathlib

noncomputable section

open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.Act

def LatHaar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (Γ : AddSubgroup V) [Countable Γ] (φ : V ≃ₜ+ V), (∀ x, φ x ∈ Γ ↔ x ∈ Γ) →
    ∀ s : Set V, IsAddFundamentalDomain Γ s μ → μ s ≠ 0 → μ s ≠ ⊤ → μ.map φ = μ

theorem latHaar : LatHaar := by
  unfold LatHaar
  intro V _ _ _ _ _ _ _ _ μ _ Γ _ φ hΓ s hs hs0 hstop
  have hmeas : Measurable φ := φ.continuous.measurable
  have : (μ.map φ).IsAddHaarMeasure := inferInstance
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map φ) μ
  have hqmp : Measure.QuasiMeasurePreserving φ μ μ := by
    refine ⟨hmeas, fun t ht => ?_⟩
    rw [hc, Measure.smul_apply, ht, smul_zero]
  let e : Γ → Γ := fun g => ⟨φ.symm g, (hΓ _).1 (by simp)⟩
  have he : Function.Bijective e := by
    constructor
    · intro g g' h
      have h2 : φ (φ.symm (g : V)) = φ (φ.symm (g' : V)) := congrArg (fun x : Γ => φ (x : V)) h
      exact Subtype.ext (by simpa using h2)
    · intro g
      exact ⟨⟨φ g, (hΓ g).2 g.2⟩, Subtype.ext (by simp [e])⟩
  have hef : ∀ g : Γ, Function.Semiconj φ (e g +ᵥ ·) (g +ᵥ ·) := by
    intro g x
    show φ ((e g : V) + x) = (g : V) + φ x
    rw [map_add]
    simp [e]
  have hs' : IsAddFundamentalDomain Γ (φ ⁻¹' s) μ := hs.preimage_of_equiv hqmp he hef
  have heq : μ (φ ⁻¹' s) = μ s := hs'.measure_eq hs
  have hνs : (μ.map φ) s = μ s := by
    rw [← heq]
    exact (φ.toHomeomorph.toMeasurableEquiv).map_apply s
  rw [hc, Measure.coe_nnreal_smul_apply] at hνs
  have h1 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) = 1 := by
    have h3 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) * μ s = 1 * μ s := by
      rw [one_mul]
      exact hνs
    exact (ENNReal.mul_left_inj hs0 hstop).1 h3
  have h2 : Measure.addHaarScalarFactor (μ.map φ) μ = 1 := by exact_mod_cast h1
  rw [hc, h2, one_smul]

end PositivityTheory.SiegelWeilFormula.Act

end
