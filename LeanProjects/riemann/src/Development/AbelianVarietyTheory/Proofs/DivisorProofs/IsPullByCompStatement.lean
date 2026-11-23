import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullBy_comp' : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left},
    X''.IsPullBy X' b' ψ → X'.IsPullBy X b φ → X''.IsPullBy X (b' ≫ b) (ψ ≫ φ) := by
  first | exact @GlobalTheory.RealMult.Obj.IsPullBy.trans | exact GlobalTheory.RealMult.Obj.IsPullBy.trans | (intros; apply GlobalTheory.RealMult.Obj.IsPullBy.trans <;> assumption)
