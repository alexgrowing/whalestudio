import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldCommutesPointTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageTrQ
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_commutes_pointTranslation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ G) (O O' : G.left.Opens), O' ≤ GlobalTheory.HeatTrans.tr G x ⁻¹ᵁ O → ∀ f : Γ(G.left, O), dd O' (pbT (GlobalTheory.HeatTrans.tr G x) f O') = pbT (GlobalTheory.HeatTrans.tr G x) (dd O f) O' := by
  first | exact @GlobalTheory.Heat.IsInv.pbT_tr | exact GlobalTheory.Heat.IsInv.pbT_tr | (intros; apply GlobalTheory.Heat.IsInv.pbT_tr <;> assumption)
