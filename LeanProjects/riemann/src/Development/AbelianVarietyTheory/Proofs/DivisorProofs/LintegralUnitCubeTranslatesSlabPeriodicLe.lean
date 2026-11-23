import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem lintegral_cube_slab_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G)
    (π : G →+ (Fin N → ℝ)) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) (U : Set G)
    (hS : MeasurableSet {w | w - ι (π w) ∈ U})
    (hfin : ∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) (hper : ∀ w, ∀ u ∈ U, φ (w + u) = φ w) (y : G) :
    μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ := by
  set S : Set G := {w | w - ι (π w) ∈ U} with hSdef
  let ν : Measure (Fin N → ℝ) := (μ.restrict S).map π
  have hν : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S) := fun A hA => by
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have : IsFiniteMeasureOnCompacts ν := ⟨fun A hA => by
    rw [hν A hA.measurableSet]
    exact lt_top_iff_ne_top.2 (hfin A hA)⟩
  have : ν.IsAddLeftInvariant := (forall_measure_preimage_add_iff ν).1 fun t A hA => by
    rw [hν A hA, hν _ (measurable_const_add t hA), ← measure_preimage_add μ (ι t) (π ⁻¹' A ∩ S)]
    congr 1
    ext w
    simp only [hSdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, map_add, hπι, add_sub_add_left_eq_sub]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have hcube : MeasurableSet (cube N) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hvol : volume (cube N) = 1 := by
    simp [cube, Real.volume_Icc_pi]
  have hνc : μ (π ⁻¹' cube N ∩ S) = c := by
    rw [← hν _ hcube, hc, Measure.smul_apply, hvol]; simp
  have hf : Measurable fun t => φ (y + ι t) := hφ.comp (measurable_const_add y |>.comp hι.measurable)
  have e1 : ∫⁻ t in cube N, φ (y + ι t) ∂ν = c * ∫⁻ t in cube N, φ (y + ι t) := by
    rw [hc, Measure.restrict_smul, lintegral_smul_measure]; rfl
  rw [hνc, ← e1, setLIntegral_map hcube hf hπ.measurable,
    Measure.restrict_restrict (hπ.measurable hcube)]
  have e2 : ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + ι (π w)) ∂μ = ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + w) ∂μ := by
    refine setLIntegral_congr_fun ((hπ.measurable hcube).inter hS) fun w hw => ?_
    have := hper (y + ι (π w)) _ hw.2
    rw [← this]
    congr 1
    abel
  rw [e2]
  calc ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + w) ∂μ ≤ ∫⁻ w, φ (y + w) ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ w, φ w ∂μ := lintegral_add_left_eq_self φ y

end GlobalTheory.ArchDecay
