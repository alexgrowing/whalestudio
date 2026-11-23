import Mathlib
import GroundTheory.PAdicHodge.FieldOfNormsResidue
import GroundTheory.PAdicHodge.FWCyclotomic
import GroundTheory.LocalFields.KroneckerWeber
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace CyclNorms

open GroundTheory.LocalField ValuativeRel

variable (p : ℕ) [Fact p.Prime]

scoped instance padicAlgCl_valuativeRel : ValuativeRel (PadicAlgCl p) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := PadicAlgCl p))

variable {p}

theorem vle_iff_norm_le (x y : PadicAlgCl p) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

scoped instance padicAlgCl_compatible : (NormedField.valuation (K := PadicAlgCl p)).Compatible :=
  Valuation.Compatible.ofValuation _

scoped instance padicAlgCl_isValuativeTopology : IsValuativeTopology (PadicAlgCl p) := by
  let : Valued (PadicAlgCl p) NNReal := NormedField.toValued
  have : (Valued.v : Valuation (PadicAlgCl p) NNReal).Compatible := padicAlgCl_compatible
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

scoped instance padicAlgCl_valuativeExtension : ValuativeExtension ℚ_[p] (PadicAlgCl p) := by
  refine ⟨fun a b ↦ ?_⟩
  rw [vle_iff_norm_le, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]

end CyclNorms

end GroundTheory.PAdicHodge
