import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelFunctionFieldTrdegEqRelDim
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldMapCompCongr
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_function_field_trdeg_eq_relDim : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O), letI := Z.fnConst.toAlgebra; Algebra.trdeg O Z.fnFld = Z.relDim := by
  first | exact @GlobalTheory.Vert.Model.trdeg_fnFld_eq_relDim_ofResidue | exact GlobalTheory.Vert.Model.trdeg_fnFld_eq_relDim_ofResidue | (intros; apply GlobalTheory.Vert.Model.trdeg_fnFld_eq_relDim_ofResidue <;> assumption)
