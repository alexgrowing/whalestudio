import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartProjectionRespectsOrthogonality
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_projection_respects_orthogonality : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegData W I) (Av : Out.PolAV (Spec (CommRingCat.of (FractionRing W)))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D Av G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∀ τ : PtHom (spMap β) (spMap β) G D.toPre.P.A, (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ (U.gt 0).pG.left) → ∀ n : ℕ, Transfer n U.cubG D.toPre.cub τ := by
  first | exact @GlobalTheory.AlphaPair.transfer_of_unif | exact GlobalTheory.AlphaPair.transfer_of_unif | (intros; apply GlobalTheory.AlphaPair.transfer_of_unif <;> assumption)
