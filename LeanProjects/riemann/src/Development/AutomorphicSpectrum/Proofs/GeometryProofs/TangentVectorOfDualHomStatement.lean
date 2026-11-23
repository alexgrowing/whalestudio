import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorOfDualHom
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_of_dual_hom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  (∀ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) →
     (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) →
     ∃ v : epsAt y ⟶ G, IsTanAt G y v ∧ v.left = spMap φ ≫ hU.fromSpec) ∧
  (∀ v : epsAt y ⟶ G, IsTanAt G y v → ∃ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) ∧
     (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) ∧ v.left = spMap φ ≫ hU.fromSpec) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der | exact GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der | (intros; apply GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der <;> assumption)
