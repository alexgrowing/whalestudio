import CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaLint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSetsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureNonzeroVectorsBoundStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

theorem theta_measure_locally_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM μ 𝓕 hμ h𝓕 T hT hd
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 M
  refine ⟨fun X => ?_⟩
  obtain ⟨K, hK, hX⟩ := exists_compact_mem_nhds X
  obtain ⟨N, r, hN, hr, hsub⟩ := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm _ (Module.finBasis F E) 1 M).2 K hK
  obtain ⟨C, hC⟩ := GlobalTheory.T.theta_measure_nonzero_vectors_bound F E σ hcm M J hJ hM _ (Module.finBasis F E) μ 𝓕 hμ h𝓕 N hN
  refine ⟨K, hX, lt_of_le_of_lt (le_trans ?_ ((measure_mono hsub).trans (hC r hr))) ENNReal.ofReal_lt_top⟩
  have hm : Measurable (K.indicator (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
  rw [← lintegral_indicator_one hK.measurableSet, ← lintegral_indicator_one hK.measurableSet,
    theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 _ _ _ hm, theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 _ _ _ hm]
  suffices hs : {X : Fin 1 → Fin M → E | gramE σ J X = T} ⊆ {X | X ≠ 0} from
    mul_le_mul_right (lintegral_mono fun h => ENNReal.tsum_mono_subtype (fun X => K.indicator
      (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (actW (AF F) σ J h⁻¹ (ratTup (AF F) X))) hs) _
  refine fun X hX h0 => hd ?_
  rw [← show gramE σ J X = T from hX, h0, Matrix.det_unique]
  simp [gramE, hE, hform]

end CompanionTheory.PlacePermOperatorBicommutantSpan
