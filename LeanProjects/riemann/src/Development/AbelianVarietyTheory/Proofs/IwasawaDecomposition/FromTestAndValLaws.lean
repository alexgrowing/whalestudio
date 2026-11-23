import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam

theorem FlagCpt.fromTest_and_val_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e), (letI := (constF e C.Y).toAlgebra; FromTest (K := c.F) (fun R _ _ => FrPt Xo c R) (fun φ y z => FrMap φ y z) C.y0) ∧ C.val 1 = 1 ∧ (∀ f g, C.val (f * g) = C.val f * C.val g) ∧ (∀ f g, C.val (f + g) = C.val f + C.val g) ∧ ∀ (a : c.F) f, C.val (a • f) = constF e C.Y a * C.val f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C
  letI := (constF e C.Y).toAlgebra
  have hA : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hT := hA C.Y.Fn C.y0
  exact ⟨hT, evalAt_one _ _ C.y0 hT, fun f g => evalAt_mul _ _ f g C.y0,
    fun f g => evalAt_add _ _ f g C.y0, fun a f => evalAt_smul _ _ a f C.y0⟩

end GlobalTheory.ShFam
