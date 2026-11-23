import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
import Development.EtaleCohomology.EtaleSheaves.ChartsPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StdChartsProof₂

theorem StdCharts_of : LateralTheory.E.StandardEtaleChartsMultivariableHensel.StdCharts := by
  intro A _ _ Z p hp
  obtain ⟨L, u, l, hu, ⟨hl, f, hf⟩, hul⟩ := hp
  have hf' : IsAffineHom f := MorphismProperty.of_isPullback hf.flip inferInstance
  let g : Z ⟶ P1 := u ≫ f
  have hU : ∀ i, IsAffineOpen (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D i) := fun i => (LateralTheory.E.ChartsPf.D_affine i).preimage g
  refine ⟨g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0, g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1, (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0).ι,
    (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1).ι, inferInstance, inferInstance, hU 0, hU 1, ?_, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hx : g x ∈ (⨆ i, LateralTheory.E.ChartsPf.D i : P1.Opens) := by rw [LateralTheory.E.ChartsPf.D_cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · refine ⟨L, u, l, f, hu, hl, hf, hul, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]; rfl
    · rw [Scheme.Opens.range_ι]; rfl

end LateralTheory.E.StdChartsProof₂
