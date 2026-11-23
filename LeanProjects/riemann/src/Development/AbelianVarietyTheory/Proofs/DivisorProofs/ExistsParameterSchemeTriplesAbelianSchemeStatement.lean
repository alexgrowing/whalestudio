import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameterScheme_triples_abelianScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens), (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∃ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), IsIntegral Y.left ∧ Smooth x.left ∧ Surjective x.left ∧ p ≫ V.ι = v.left ∧ (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) ∧ Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ := by
  first | exact @GlobalTheory.ParamTriple.exists_param | exact GlobalTheory.ParamTriple.exists_param | (intros; apply GlobalTheory.ParamTriple.exists_param <;> assumption)
