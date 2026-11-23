import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SlopeRamifiedInducedPrimeField
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.MetricDisjointSupportOrthogonal
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.PolynomialFunctionFrameTranslate
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.PSplitT

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms

theorem slope_formula_of_isometry {D : D7} {u : D.what₂.Word} (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : Forms0 D u)
    (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hI : DiamondIsometry D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_split hS Tf hA (splitAtT_of_tied Tf.atT) (metric_disjoint_support_orthogonal Tf) hI

theorem slope_formula_of_character_finite {D : D7} {u : D.what₂.Word} (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : Forms0 D u) (hC : ChiFin0 Tf)
    (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_isometry hS Tf hA (diamond_isometry_at_infinity Tf hC hA)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
