import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyEmbedsComplex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_embeds_complex : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp k) (d : ℕ), IsArithVar q d → Nonempty (B.functionField →+* ℂ) := by
  first | exact @GlobalTheory.FnEmb.nonempty_functionField_ringHom_complex | exact GlobalTheory.FnEmb.nonempty_functionField_ringHom_complex | (intros; apply GlobalTheory.FnEmb.nonempty_functionField_ringHom_complex <;> assumption)
