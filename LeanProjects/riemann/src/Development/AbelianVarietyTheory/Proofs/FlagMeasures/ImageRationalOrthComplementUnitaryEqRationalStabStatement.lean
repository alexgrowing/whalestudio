import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImageRationalOrthComplementUnitaryEqRationalStab
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.image_rationalOrthComplementUnitary_eq_rationalStabilizer : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf), IsInfEmb D x A jv → IsFinEmb D x A jf → embA D jv jf '' D.inst.GFset = stabF I x := by
  first | exact @GlobalTheory.StabUnfold.image_rational_eq_stab | exact GlobalTheory.StabUnfold.image_rational_eq_stab | (intros; apply GlobalTheory.StabUnfold.image_rational_eq_stab <;> assumption)
