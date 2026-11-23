import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareDiagonalRelAmple
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_diagonal_rel_ample : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A' (((X.P c).pull φ₂).pull (lift (𝟙 A') (𝟙 A')).left) := by
  first | exact @GlobalTheory.RealMult.Obj.relAmple_diag_of_isGrpPullback | exact GlobalTheory.RealMult.Obj.relAmple_diag_of_isGrpPullback | (intros; apply GlobalTheory.RealMult.Obj.relAmple_diag_of_isGrpPullback <;> assumption)
