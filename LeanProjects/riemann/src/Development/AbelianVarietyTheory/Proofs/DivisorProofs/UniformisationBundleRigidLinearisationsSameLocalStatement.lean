import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleRigidLinearisationsSameLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationBundle_rigidLinearisations_same_localUnits : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (s : Sp R' ⟶ Sp R') (f₁ f₂ : G'.left ⟶ G'.left), f₁ = f₂ → ∀ (he₁ : eSec G' ≫ f₁ = s ≫ eSec G') (he₂ : eSec G' ≫ f₂ = s ≫ eSec G') (w₁ : LB.Iso U'.LG.L (U'.LG.L.pull f₁)) (w₂ : LB.Iso U'.LG.L (U'.LG.L.pull f₂)), w₁.IsGen → w₂.IsGen → LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₁ s he₁ U'.LG.L U'.LG.rig) → LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₂ s he₂ U'.LG.L U'.LG.rig) → ∀ (z : G'.left) (j k : U'.LG.L.ι), z ∈ U'.LG.L.U k → f₁ z ∈ U'.LG.L.U j → gw w₁ (𝟙 G'.left) z j k = gw w₂ (𝟙 G'.left) z j k := by
  first | exact @GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified | exact GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified | (intros; apply GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified <;> assumption)
