import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FieldBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_valued_lift_field_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)) (lam : Ix → DomWeight n) (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam), IoLFRec c (fun t => embF c (pl t)) lam a io hw → ∃ (io' : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (hw' : VVc c' lam), IoLFRec c' (fun t => embF c' (pl t)) lam a io' hw' ∧ IoOver hle lam io io' := by
  first | exact @GlobalTheory.IoExtend.exists_ioLFRec_over | exact GlobalTheory.IoExtend.exists_ioLFRec_over | (intros; apply GlobalTheory.IoExtend.exists_ioLFRec_over <;> assumption)
