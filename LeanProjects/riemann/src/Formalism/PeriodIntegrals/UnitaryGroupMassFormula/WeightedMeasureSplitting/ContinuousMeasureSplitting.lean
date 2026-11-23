import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousTensMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContSplit

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct

theorem continuous_haMap {F E : Type} [Field F] [Field E] [Algebra F E]
    {R R' : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [CommRing R'] [Algebra F R']
    [TopologicalSpace R'] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (φ : R →ₐ[F] R')
    (hφ : Continuous (tensMap (E := E) φ)) : Continuous (haMap σ J φ) := by
  have hmat : Continuous (fun g : HA R σ J => (HA.mat R σ J g : GL (Fin n) (R ⊗[F] E))) :=
    continuous_subtype_val
  have key : Continuous (fun g : HA R σ J =>
      (Formalism.UG.bc (tensMap (E := E) φ) (HA.mat R σ J g) : GL (Fin n) (R' ⊗[F] E))) := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous (fun g : HA R σ J =>
        ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map
          (tensMap (E := E) φ))
      exact (Units.continuous_val.comp hmat).matrix_map hφ
    · change Continuous (fun g : HA R σ J =>
        (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map
          (tensMap (E := E) φ))
      exact (Units.continuous_coe_inv.comp hmat).matrix_map hφ
  exact continuous_induced_rng.2 key

theorem continuous_measure_splitting : ContSplit := by
  intro F E _ _ _ _ _ σ n J _
  have : FiniteDimensional F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  exact (continuous_haMap σ J (fstA F)
      (continuous_tensMap (AF F) (fstA F) continuous_fstA)).prodMk
    (continuous_haMap σ J (sndA F) (continuous_tensMap (AF F) (sndA F) continuous_sndA))

end PI.UnitaryGroupMassFormula.MeasWCore
