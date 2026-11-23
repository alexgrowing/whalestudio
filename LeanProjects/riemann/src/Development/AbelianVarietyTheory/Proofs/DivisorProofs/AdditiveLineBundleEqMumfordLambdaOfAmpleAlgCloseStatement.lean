import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleEqMumfordLambdaOfAmpleAlgClose
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveLineBundle_eq_mumfordLambda_of_ample_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ N : LB (A ⊗ 𝟙_ (Over (Sp K))).left, Fam A N → ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, Same A N (abelian₂ A L) (𝟙 _) a := by
  first | exact @GlobalTheory.AddLineField.additive_eq_lam_of_ample | exact GlobalTheory.AddLineField.additive_eq_lam_of_ample | (intros; apply GlobalTheory.AddLineField.additive_eq_lam_of_ample <;> assumption)
