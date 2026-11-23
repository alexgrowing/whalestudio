import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_section_pullback : ∀ (S S' : Scheme.{0}) (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (T : Over S') (w : Over.mk (T.hom ≫ f) ⟶ G),
      ∃ σ : T ⟶ G', σ.left ≫ φ = w.left ∧ ∀ k : ℕ, w ^ k = 1 → σ ^ k = 1 := by
  first | exact @GlobalTheory.grpPullback_lift_torsion | exact GlobalTheory.grpPullback_lift_torsion | (intros; apply GlobalTheory.grpPullback_lift_torsion <;> assumption)
