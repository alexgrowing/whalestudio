import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitHomeoApply
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem isHaarMeasure_map_splitHomeo :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure], (∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν) → (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)).IsHaarMeasure := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι ν _ μ₁ _ hconj
  have hclosed : IsClosed (π.ker : Set P) := by
    have hk : (π.ker : Set P) = π ⁻¹' {1} := by
      ext p
      simp
    rw [hk]
    exact isClosed_singleton.preimage hπ
  have : LocallyCompactSpace π.ker := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have : SigmaCompactSpace π.ker := inferInstance
  have : SigmaFinite ν := inferInstance
  set Φ := splitHomeo ι π hι hπ hπι with hΦdef
  have hΦm : Measurable Φ := Φ.continuous.measurable
  have hinv : (Measure.map Φ (ν.prod μ₁)).IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    set k₀ := kerPart ι π hπι g
    have hcm : Measurable (fun m : π.ker => MulAut.conjNormal (ι (π g)) m) :=
      ((continuous_conj ι π hι).comp (Continuous.prodMk_right (π g))).measurable
    have hfm : Measurable (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) :=
      (measurable_const_mul k₀).comp hcm
    have hhm : Measurable (fun u : G₁ => π g * u) := measurable_const_mul _
    have e1 : Measure.map (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) ν = ν := by
      have hsplit : (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) =
          (fun x => k₀ * x) ∘ (fun m : π.ker => MulAut.conjNormal (ι (π g)) m) := rfl
      rw [hsplit, ← Measure.map_map (measurable_const_mul k₀) hcm, hconj, map_mul_left_eq_self]
    have e2 : Measure.map (fun u : G₁ => π g * u) μ₁ = μ₁ := map_mul_left_eq_self μ₁ _
    have hcomp : (fun x => g * x) ∘ Φ =
        Φ ∘ Prod.map (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) (fun u : G₁ => π g * u) := by
      funext z
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, hΦdef, splitHomeo_apply]
      exact mul_split ι π hπι g z.1 z.2
    rw [Measure.map_map (measurable_const_mul g) hΦm, hcomp, ← Measure.map_map hΦm (hfm.prodMap hhm),
      ← Measure.map_prod_map ν μ₁ hfm hhm, e1, e2]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : P)
  have hKm : MeasurableSet K := hK.measurableSet
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK ⟨1, mem_interior_iff_mem_nhds.mpr hK1⟩ ?_ ?_
  · rw [Measure.map_apply hΦm hKm]
    have hopen : IsOpen (Φ ⁻¹' interior K) := isOpen_interior.preimage Φ.continuous
    have hne : (Φ ⁻¹' interior K).Nonempty := by
      obtain ⟨z, hz⟩ := Φ.surjective 1
      refine ⟨z, ?_⟩
      show Φ z ∈ interior K
      rw [hz]
      exact mem_interior_iff_mem_nhds.mpr hK1
    exact ((hopen.measure_pos _ hne).trans_le (measure_mono (Set.preimage_mono interior_subset))).ne'
  · rw [Measure.map_apply hΦm hKm]
    exact (Φ.isCompact_preimage.mpr hK).measure_lt_top.ne

end GlobalTheory.CompanionTheory.SplitExtLat
