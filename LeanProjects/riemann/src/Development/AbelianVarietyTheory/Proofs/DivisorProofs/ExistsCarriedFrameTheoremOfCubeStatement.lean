import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCube
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_carriedFrame_theoremOfCube : ∀ {S : Scheme.{0}} (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (L : RigLB G') (c : CubicalStr G' L) (θ : L.L.Sec) (T : Over S) (x a b c' : T ⟶ G') (W : T.left.Opens), (∀ g ∈ cubeTen x a b c', W ≤ g.left ⁻¹ᵁ secNz θ) → ∃ τ : ∀ k : L.L.ι, Γ(T.left, W ⊓ x.left ⁻¹ᵁ L.L.U k)ˣ, FrameAlong L.L x.left W τ ∧ ∀ (f : G'.left ⟶ G'.left) (fS : S ⟶ S) (hc : IsGrpPullback G' G' fS f) (w : LB.Iso L.L (L.L.pull f)), w.IsGen → PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) L.rig L.rig fS → PMaps w (thφ G' (x3 G')) (thφ G' (x3 G')) thε c.t c.t (cubeMapOf hc).F3 → SecCarried L.L θ f w → ∀ hT : T.left ⟶ T.left, hT ≫ T.hom = T.hom ≫ fS → x.left ≫ f = hT ≫ x.left → a.left ≫ f = hT ≫ a.left → b.left ≫ f = hT ≫ b.left → c'.left ≫ f = hT ≫ c'.left → FrameCarriedAlong L.L x.left W τ f w hT := by
  first | exact @GlobalTheory.Mum.exists_carried_frame_of_cubeTen | exact GlobalTheory.Mum.exists_carried_frame_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_carried_frame_of_cubeTen <;> assumption)
