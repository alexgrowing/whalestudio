import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

theorem chart_inter_factor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ (R1 R2 : Type) [CommRing R1] [CommRing R2] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → ∃ (A : Type) (_ : CommRing A) (w : Sp A ⟶ X) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion w ∧ spMap a1 ≫ ξ1 = w ∧ spMap a2 ≫ ξ2 = w ∧ Set.range w = Set.range ξ1 ∩ Set.range ξ2 := by
  intro R _ X s hP R1 R2 _ _ ξ1 ξ2 h1 h2
  obtain ⟨N, i, hi, hs⟩ := hP
  have : IsProper (PSpace.str R N) := isProper_str R N
  have : IsProper s := by rw [← hs]; infer_instance
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  have hU : IsAffineOpen (ξ1.opensRange ⊓ ξ2.opensRange) :=
    (isAffineOpen_opensRange ξ1).inf (isAffineOpen_opensRange ξ2)
  have hr1 : Set.range hU.fromSpec.base ⊆ Set.range ξ1.base := by
    rw [hU.range_fromSpec]; intro x hx; exact hx.1
  have hr2 : Set.range hU.fromSpec.base ⊆ Set.range ξ2.base := by
    rw [hU.range_fromSpec]; intro x hx; exact hx.2
  refine ⟨Γ(X, ξ1.opensRange ⊓ ξ2.opensRange), inferInstance, hU.fromSpec,
    (Spec.preimage (IsOpenImmersion.lift ξ1 hU.fromSpec hr1)).hom,
    (Spec.preimage (IsOpenImmersion.lift ξ2 hU.fromSpec hr2)).hom, inferInstance, ?_, ?_, ?_⟩
  · simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  · simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  · show Set.range hU.fromSpec.base = _
    rw [hU.range_fromSpec]
    rfl

end GlobalTheory.UnitGlue
