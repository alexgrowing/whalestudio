import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (θ : P.L.L.Sec) (T : Over S) (x a b c : T ⟶ G) (W : T.left.Opens), (∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) → ∃ t : LB.Gen (P.L.L.pull (W.ι ≫ x.left)), t.IsGen := by
  first | exact @GlobalTheory.Mum.exists_gen_of_cubeTen | exact GlobalTheory.Mum.exists_gen_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_gen_of_cubeTen <;> assumption)
