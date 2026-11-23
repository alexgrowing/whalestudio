import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

private lemma measurable_lineOf' {N : ℕ} : Measurable (lineOf (N := N)) := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  rw [continuousOn_iff_continuous_domRestrict]
  have h : ({0}ᶜ : Set (Fin (N + 1) → ℂ)).domRestrict lineOf =
      fun v => Projectivization.mk' ℂ ⟨v.1, v.2⟩ := by
    funext ⟨v, hv⟩; exact lineOf_of_ne hv
  rw [h]
  exact ProjTopology.continuous_mk'.comp (continuous_subtype_val.subtype_mk _)

private lemma continuous_unitaryAct' {N : ℕ} (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) :
    Continuous (unitaryAct (N := N) U) := by
  rw [ProjTopology.continuous_iff]
  have h : unitaryAct (N := N) U ∘ Projectivization.mk' ℂ = fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} =>
      Projectivization.mk' ℂ ⟨Matrix.toLin' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) v.1,
        fun h0 => v.2 (unitary_injective U (by rw [h0, map_zero]))⟩ := by
    funext ⟨v, hv⟩; rfl
  rw [h]
  exact ProjTopology.continuous_mk'.comp
    (((LinearMap.continuous_of_finiteDimensional _).comp continuous_subtype_val).subtype_mk _)

theorem UnitaryInv.proof (hE : AmbEq.Statement) (hU : AmbUnitary.Statement) :
    UnitaryInv.Statement := by
  intro N U
  have hUm : Measurable (unitaryAct (N := N) U) := (continuous_unitaryAct' U).measurable
  set L := Matrix.toLin' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) with hLdef
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hne : ∀ᵐ v ∂ambMeasure N, v ≠ 0 :=
    (withDensity_absolutelyContinuous _ _).ae_le (Measure.ae_ne volume 0)
  have hae : unitaryAct U ∘ lineOf =ᵐ[ambMeasure N] lineOf ∘ L := by
    filter_upwards [hne] with v hv
    have hLv : L v ≠ 0 := fun h0 => hv (unitary_injective U (by rw [map_zero]; exact h0))
    simp only [Function.comp_apply, lineOf_of_ne hv, lineOf_of_ne hLv, unitaryAct_mk]
    rfl
  refine ⟨hUm, ?_⟩
  rw [hE N, Measure.map_smul, Measure.map_map hUm measurable_lineOf', Measure.map_congr hae,
    ← Measure.map_map measurable_lineOf' hLm, hU N U]

end FSInv

end

end GroundTheory.Heights₂.Heights
