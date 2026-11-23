import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField MeasureTheory
open scoped TensorProduct ENNReal Pointwise

namespace GlobalTheory.TamUnf

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def finSU (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J) :=
  (Matrix.GeneralLinearGroup.det.comp (HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J).subtype).ker

theorem mem_finSU {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    {k : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J} :
    k ∈ finSU σ J ↔ ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J k : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).det = 1 := by
  show Matrix.GeneralLinearGroup.det ((HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J).subtype k) = 1 ↔ _
  rw [Units.ext_iff]
  rfl

end Fin

theorem exists_haar_prod {G A H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ₀ : Measure A) [μ₀.IsHaarMeasure] (e : G ≃ₜ* A × H) {K : Set H} (hKo : IsOpen K) (hKc : IsCompact K)
    (hK1 : (1 : H) ∈ K) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ B : Set A, MeasurableSet B → ∀ t : H,
      μ (e ⁻¹' (B ×ˢ (t • K))) = μ₀ B * c := by
  haveI : IsTopologicalGroup G := e.toHomeomorph.isInducing.topologicalGroup (e : G →* A × H)
  let K0 : TopologicalSpace.PositiveCompacts H :=
    ⟨⟨K, hKc⟩, by
      show (interior K).Nonempty
      rw [hKo.interior_eq]; exact ⟨1, hK1⟩⟩
  haveI : (c • Measure.haarMeasure K0).IsHaarMeasure := Measure.IsHaarMeasure.smul _ hc0 hct
  let m : Measure (A × H) := μ₀.prod (c • Measure.haarMeasure K0)
  haveI : m.IsHaarMeasure := inferInstanceAs ((μ₀.prod (c • Measure.haarMeasure K0)).IsHaarMeasure)
  refine ⟨m.map e.symm, e.symm.isHaarMeasure_map m, fun B hB t => ?_⟩
  have hme : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  rw [hme.map_apply]
  have : e.symm ⁻¹' (e ⁻¹' (B ×ˢ (t • K))) = B ×ˢ (t • K) := by
    ext x; simp
  rw [this, Measure.prod_prod, Measure.smul_apply, measure_smul, smul_eq_mul]
  have h1 : Measure.haarMeasure K0 K = 1 := Measure.haarMeasure_self
  rw [h1, mul_one]

end GlobalTheory.TamUnf
