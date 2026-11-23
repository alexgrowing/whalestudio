import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem covolume_ne_top_of_continuousMulEquiv : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (Γ : Subgroup G) (Λ : Subgroup H) [Countable Γ], (∀ g, g ∈ Γ ↔ e g ∈ Λ) → (∀ μ : Measure G, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤) → ∀ (π : Measure H) (𝓜 : Set H), π.IsHaarMeasure → IsFundamentalDomain Λ 𝓜 π → π 𝓜 ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ e Γ Λ _ hmem hfin π 𝓜 hπ h𝓜
  let E : G ≃ᵐ H := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun _ => rfl
  set μ : Measure G := π.map E.symm with hμdef
  have hμ : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map π e.symm
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving E μ π := by
    refine ⟨E.measurable, ?_⟩
    rw [hμdef, Measure.map_map E.measurable E.symm.measurable]
    simp only [MeasurableEquiv.self_comp_symm, Measure.map_id]
    exact Measure.AbsolutelyContinuous.rfl
  let φ : Λ → Γ := fun l => ⟨e.symm l, (hmem _).2 (by simpa using l.2)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have := congrArg (fun x : Γ => e (x : G)) hab
      simpa [φ] using this
    · intro g
      refine ⟨⟨e g, (hmem g).1 g.2⟩, ?_⟩
      apply Subtype.ext; simp [φ]
  have hsemi : ∀ l : Λ, Function.Semiconj E (φ l • ·) (l • ·) := by
    intro l x
    show e ((e.symm l : G) * x) = (l : H) * e x
    simp [map_mul]
  have hF := h𝓜.preimage_of_equiv hqmp hφ hsemi
  have hlt := hfin μ hμ _ hF
  have : μ (E ⁻¹' 𝓜) = π 𝓜 := by
    rw [hμdef, MeasurableEquiv.map_apply]
    congr 1
    ext x; simp
  rw [this] at hlt
  exact hlt.ne

end GlobalTheory.SphEis
