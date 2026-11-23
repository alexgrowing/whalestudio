import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [CommRing R₀] [Nontrivial R₀] (π : R →+* R₀), Function.Surjective π → ∀ (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left), P.IsLB → (∃ t : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → ∀ (L : LB B.left) (L₀ : LB B₀.left), L.IsLB → L₀.IsLB → LBIso (L.pull i) L₀ → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → LBIso (abelian₂ B L) P := by
  first | exact @GlobalTheory.PolRigid.lbIso_lam_of_quotient | exact GlobalTheory.PolRigid.lbIso_lam_of_quotient | (intros; apply GlobalTheory.PolRigid.lbIso_lam_of_quotient <;> assumption)
