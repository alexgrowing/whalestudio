import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHaarMeasureComapSubtype

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.NormFib

theorem map_norm_add_translate_eq_smul : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : NNReal,
  (multHaar E).map (normUnits F E) + (multHaar E).map (fun x => a * normUnits F E x) = κ • multHaar F := by
  intro F E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc a ha
  have hO : IsOpen ((normUnits F E).range : Set Fˣ) :=
    GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_range_normUnits (K := F) (E := E)
  obtain ⟨c, -, hmap⟩ := exists_map_eq_smul_restrict (normUnits F E)
    (isProperMap_normUnits F E) hO (multHaar E) (multHaar F)
  set H : Set Fˣ := ((normUnits F E).range : Set Fˣ) with hH
  have hHm : MeasurableSet H := hO.measurableSet
  have hmeasN : Measurable (normUnits F E) := (continuous_normUnits F E).measurable
  have hmul : Measurable (fun y : Fˣ => a * y) := measurable_const_mul a
  have hcompl : (fun y : Fˣ => a * y) ⁻¹' Hᶜ = H := by
    ext y
    have h := Subgroup.mul_mem_iff_of_index_two (index_range_normUnits_eq_two F E) (a := a) (b := y)
    simp only [Set.mem_preimage, Set.mem_compl_iff, hH, SetLike.mem_coe]
    tauto
  have hsecond : (multHaar E).map (fun x => a * normUnits F E x) =
      c • (multHaar F).restrict Hᶜ := by
    have e1 : (multHaar E).map (fun x => a * normUnits F E x) =
        ((multHaar E).map (normUnits F E)).map (fun y : Fˣ => a * y) :=
      (Measure.map_map hmul hmeasN).symm
    have e2 : (multHaar F).restrict Hᶜ = ((multHaar F).restrict H).map (fun y : Fˣ => a * y) := by
      conv_lhs => rw [← map_mul_left_eq_self (multHaar F) a]
      rw [(measurableEmbedding_mulLeft a).restrict_map, hcompl]
    rw [e1, hmap, e2, Measure.map_smul]
  refine ⟨c, ?_⟩
  rw [hsecond, hmap, ← smul_add, Measure.restrict_add_restrict_compl hHm]

end GlobalTheory.CompanionTheory.NormFib
