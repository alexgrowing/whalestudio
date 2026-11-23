import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSectionValueProductExpansionTerms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqZeroWeightIndependenceLevelStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_section_value_product_expansion_terms : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), Act D₁ D₂ b h g g' → ∀ (j j' : ℕ) (w : Frm D₂ F j g'.b) (w' : Frm D₁ F j' g.b) (χ : D₂.X) (δ : D₁.X) (u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ)), Nrm u → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' δ) (y y' : F), MixedConv.IsCoefB j g' w χ f y → MixedConv.IsCoefB j' g w' δ f' y' → ∀ (z : (TF (R := R) F).left) (J), Good (JN D₁ D₂) z J → sval f (g.b.left ≫ b.left) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J * val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J)).val = cst F z (y * y') * (rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s (h χ + δ)) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹).val := by
  first | exact @GlobalTheory.Mum.Two.Mix.val_mixed_eval | exact GlobalTheory.Mum.Two.Mix.val_mixed_eval | (intros; apply GlobalTheory.Mum.Two.Mix.val_mixed_eval <;> assumption)
