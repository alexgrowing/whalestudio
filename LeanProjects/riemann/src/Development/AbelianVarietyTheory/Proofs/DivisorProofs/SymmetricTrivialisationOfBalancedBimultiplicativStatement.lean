import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTrivialisationOfBalancedBimultiplicativ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_trivialisation_of_balanced_bimultiplicative : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (M : RigLB B) (cub : CubicalStr B M) (O : Type) [CommRing O] [StarRing O] (act : RingAct B O),
    (∀ a : O, RosatiAdj B M.L (act.act a) (act.act (star a))) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (c : X → (𝟙_ (Over (Sp R)) ⟶ B)), (∀ y y', c (y + y') = c y * c y') →
    (∀ (a : O) (y : X), c (a • y) = c y ≫ act.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    ∀ τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ →
    ∃ τ' : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ' ∧
      ∀ y z p J, Good M.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J := by
  first | exact @GlobalTheory.SymTau.symm_of_bal | exact GlobalTheory.SymTau.symm_of_bal | (intros; apply GlobalTheory.SymTau.symm_of_bal <;> assumption)
