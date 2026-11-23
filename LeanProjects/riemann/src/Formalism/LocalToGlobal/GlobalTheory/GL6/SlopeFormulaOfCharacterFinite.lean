import Formalism.LocalToGlobal.GlobalTheory.GL6.SlopeRamifiedInducedPrimeField
import Formalism.LocalToGlobal.GlobalTheory.GL6.MetricDisjointSupportOrthogonal
import Formalism.LocalToGlobal.GlobalTheory.GL6.PolynomialFunctionFrameTranslate
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms

theorem slope_formula_of_isometry {D : D7} {u : D.what₂.Word} (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u)
    (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hI : DiamondIsometry D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_diamonds hS Tf hA (diamond_elements_exist_all Tf) (metric_disjoint_support_orthogonal Tf) hI

theorem slope_formula_of_character_finite {D : D7} {u : D.what₂.Word} (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u) (hC : ChiFin Tf)
    (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_isometry hS Tf hA (diamond_isometry_at_infinity Tf hC hA)

theorem ramified_lattice_of_length
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u → Formalism.MainNotions.product_first_zeroth_parts.admS D u → LatticeInclusionLength D u) :
    RamifiedLatticeFamily :=
  ramified_lattice_of_slope_and_length (fun _ _ Tf _ => splitAtT_of_tied Tf.atT) fun D u hF hS hA => by
    have hL := h D u hF hS hA
    obtain ⟨Tf, hC⟩ := hF
    exact ⟨slope_formula_of_character_finite hS Tf hC hA, hL⟩

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
