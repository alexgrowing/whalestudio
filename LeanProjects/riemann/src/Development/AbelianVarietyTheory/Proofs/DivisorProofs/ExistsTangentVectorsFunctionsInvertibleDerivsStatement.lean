import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorsFunctionsInvertibleDerivs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentVectors_functions_invertible_derivs : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] {K : Type} [Field K] (z : Sp K ⟶ Y), ∃ (O : Y.Opens) (_ : ⊤ ≤ z ⁻¹ᵁ O) (x : Fin D → Γ(Y, O)) (w : Fin D → (Sp (DualNumber K) ⟶ Y)), (∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z) ∧ ∀ hwO : (∀ b, ⊤ ≤ w b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (x a)).snd).det ≠ 0 := by
  first | exact @GlobalTheory.TanVec.exists_tangent_matrix | exact GlobalTheory.TanVec.exists_tangent_matrix | (intros; apply GlobalTheory.TanVec.exists_tangent_matrix <;> assumption)
