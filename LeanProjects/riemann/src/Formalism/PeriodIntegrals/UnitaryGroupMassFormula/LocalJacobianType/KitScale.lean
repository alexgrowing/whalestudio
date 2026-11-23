import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMul

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem norm_sc (hfin : Module.finrank F E = 2) (x : Fv F v) :
    Algebra.norm (Fv F v) (sc (E := E) v x) = x ^ 2 := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have h1 : sc (E := E) v x = algebraMap (Fv F v) (Fv F v ⊗[F] E) x := by
    simp [PI.LocJacTyp.sc, Algebra.TensorProduct.algebraMap_apply]
  rw [h1, Algebra.norm_algebraMap, Module.finrank_baseChange, hfin]

theorem boxScale {ι : Type} [Fintype ι] (hfin : Module.finrank F E = 2)
    (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure] (x : ι → Fv F v) (hx : ∀ i, x i ≠ 0) :
    (μ (Set.univ.pi fun i => {c | sc (E := E) v (x i) * c ∈ OEv (E := E) v})).toReal =
      (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (x i) ^ 2)⁻¹ := by
  have hu : ∀ i, IsUnit (sc (E := E) v (x i)) := fun i =>
    (isUnit_iff_ne_zero.2 (hx i)).map (algebraMap (Fv F v) (Fv F v ⊗[F] E))
  rw [BM.box_measure_mul (E := E) v ι μ _ hu]
  simp only [norm_sc v hfin, absV_pow]

end PI.UnitaryGroupMassFormula.LocJacTyp
