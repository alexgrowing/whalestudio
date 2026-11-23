import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareActionBundleIso
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_action_bundle_iso : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c c' : 𝔠.elt) (a : 𝓞 F),
      LBIso ((X.P c).pull φ₂) (((X.P c).pull φ₂).pull (lift (snd A' A') (fst A' A')).left) ∧
      LBIso ((X.P c').pull φ₂) (LB.div ((X.P (c + c')).pull φ₂) ((X.P c).pull φ₂)) ∧
      LBIso ((X.P (a • c)).pull φ₂) (((X.P c).pull φ₂).pull (lift (fst A' A') (snd A' A' ≫ rm'.act a)).left) := by
  first | exact @GlobalTheory.RealMult.PullPol.pol_pull | exact GlobalTheory.RealMult.PullPol.pol_pull | (intros; apply GlobalTheory.RealMult.PullPol.pol_pull <;> assumption)
