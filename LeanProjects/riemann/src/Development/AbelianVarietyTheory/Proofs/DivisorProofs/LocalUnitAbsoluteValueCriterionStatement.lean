import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitAbsoluteValueCriterion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCountStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unit_absolute_value_criterion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) [Fact (resP v).Prime] (k : ℕ) (gn : Fin k → ℝ), (∀ l, 0 < gn l) → ∀ b : AlgebraicClosure F, (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) ≤ 1 ↔ ‖ioOf (resP v) ε b‖ ≤ ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) = 1 ↔ ‖ioOf (resP v) ε b‖ = ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) < 1 ↔ ‖ioOf (resP v) ε b‖ < ∏ l, gn l) := by
  first | exact @GlobalTheory.ShFam.Pad.w_mul_exp_cmp_iff | exact GlobalTheory.ShFam.Pad.w_mul_exp_cmp_iff | (intros; apply GlobalTheory.ShFam.Pad.w_mul_exp_cmp_iff <;> assumption)
