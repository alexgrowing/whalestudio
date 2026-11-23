import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem ringOfIntegers_equiv_bar_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E), τ (H.bar a) = H.bar (τ a) := by
  intro E _ _ _ H τ a
  have hM : (nonZeroDivisors (𝓞 E)).map (τ : 𝓞 E →* 𝓞 E) = nonZeroDivisors (𝓞 E) := by
    exact MulEquivClass.map_nonZeroDivisors τ
  let τE : E ≃+* E := IsLocalization.ringEquivOfRingEquiv E E τ hM
  have hτE : ∀ x : 𝓞 E, τE (x : E) = ((τ x : 𝓞 E) : E) := by
    intro x
    exact IsLocalization.ringEquivOfRingEquiv_eq hM x
  obtain ⟨ψ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply RingOfIntegers.ext
  rw [← hτE, H.bar_eq, H.bar_eq, ← hτE]
  apply ψ.injective
  have h1 := IsCMField.complexEmbedding_complexConj E (ψ.comp (τE : E →+* E)) (a : E)
  have h2 := IsCMField.complexEmbedding_complexConj E ψ (τE (a : E))
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1
  rw [h1, h2]

end GlobalTheory
