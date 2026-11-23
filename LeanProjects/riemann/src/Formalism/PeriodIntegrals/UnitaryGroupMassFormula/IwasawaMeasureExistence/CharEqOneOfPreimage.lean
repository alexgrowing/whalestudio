import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.LocallyCompactAEf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MulEquivHaarCharEqOfChart

noncomputable section

namespace PI.IwaMeasEx.MH

open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal

section Gen

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem nnreal_eq_of_smul (μ : Measure A) [μ.IsAddHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts A) := inferInstance
  have h0 : μ K ≠ 0 := (measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have ht : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hK := congrArg (fun ν : Measure A => ν K) h
  simp only [Measure.smul_apply, nnreal_smul_coe_apply] at hK
  exact_mod_cast (ENNReal.mul_left_inj h0 ht).1 hK

theorem char_eq_of_map (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (φ : A ≃ₜ+ A) {c : ℝ≥0} (hc : c ≠ 0)
    (h : μ.map φ = c • μ) : addEquivAddHaarChar φ = c⁻¹ := by
  have h1 := addEquivAddHaarChar_smul_map μ φ
  rw [h, smul_smul] at h1
  exact eq_inv_of_mul_eq_one_left (nnreal_eq_of_smul μ (h1.trans (one_smul _ _).symm))

theorem map_char (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (φ : A ≃ₜ+ A) :
    μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
  conv_rhs => rw [← addEquivAddHaarChar_smul_map μ φ]
  rw [smul_smul, inv_mul_cancel₀ (addEquivAddHaarChar_pos φ).ne', one_smul]

variable {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
  [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem char_transport (e : A ≃ₜ+ B) (φ : A ≃ₜ+ A) :
    addEquivAddHaarChar ((e.symm.trans φ).trans e) = addEquivAddHaarChar φ := by
  have : ((addHaar : Measure A).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have : ((addHaar : Measure A).map e).Regular := Regular.map e.toHomeomorph
  refine (char_eq_of_map ((addHaar : Measure A).map e) _
    (inv_ne_zero (addEquivAddHaarChar_pos φ).ne') ?_).trans (inv_inv _)
  have hcomp : ((e.symm.trans φ).trans e : B → B) ∘ e = e ∘ φ := by
    funext x
    simp
  rw [Measure.map_map (map_continuous _).measurable (map_continuous e).measurable, hcomp,
    ← Measure.map_map (map_continuous e).measurable (map_continuous φ).measurable,
    map_char (addHaar : Measure A) φ, Measure.map_smul]

def prodE (φ : A ≃ₜ+ A) (ψ : B ≃ₜ+ B) : A × B ≃ₜ+ A × B where
  toFun p := (φ p.1, ψ p.2)
  invFun p := (φ.symm p.1, ψ.symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp
  continuous_toFun := (φ.continuous.comp continuous_fst).prodMk (ψ.continuous.comp continuous_snd)
  continuous_invFun := (φ.symm.continuous.comp continuous_fst).prodMk (ψ.symm.continuous.comp continuous_snd)

theorem char_prod (φ : A ≃ₜ+ A) (ψ : B ≃ₜ+ B) :
    addEquivAddHaarChar (prodE φ ψ) = addEquivAddHaarChar φ * addEquivAddHaarChar ψ := by
  have hmap : ((addHaar : Measure A).prod (addHaar : Measure B)).map (prodE φ ψ) =
      ((addEquivAddHaarChar φ)⁻¹ * (addEquivAddHaarChar ψ)⁻¹) •
        ((addHaar : Measure A).prod (addHaar : Measure B)) := by
    rw [show (prodE φ ψ : A × B → A × B) = Prod.map φ ψ from rfl,
      ← Measure.map_prod_map _ _ (map_continuous φ).measurable (map_continuous ψ).measurable,
      map_char (addHaar : Measure A) φ, map_char (addHaar : Measure B) ψ,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [char_eq_of_map _ _ (mul_ne_zero (inv_ne_zero (addEquivAddHaarChar_pos φ).ne')
    (inv_ne_zero (addEquivAddHaarChar_pos ψ).ne')) hmap, mul_inv, inv_inv, inv_inv]

end Gen

end PI.IwaMeasEx.MH

end
