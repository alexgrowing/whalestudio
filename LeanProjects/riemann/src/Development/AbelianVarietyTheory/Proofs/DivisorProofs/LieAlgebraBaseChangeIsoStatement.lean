import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIso
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_base_change_iso : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap (algebraMap R R')) φ →
    ∃ e : R' ⊗[R] X.Lie ≃ₗ[R'] X'.Lie, ∀ v v', LieCorr (algebraMap R R') φ v v' ↔ v' = e (1 ⊗ₜ v) := by
  first | exact @GlobalTheory.RealMult.Obj.lieBaseChange_equiv | exact GlobalTheory.RealMult.Obj.lieBaseChange_equiv | (intros; apply GlobalTheory.RealMult.Obj.lieBaseChange_equiv <;> assumption)
