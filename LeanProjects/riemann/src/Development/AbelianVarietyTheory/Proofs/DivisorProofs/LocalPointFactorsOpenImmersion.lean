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

namespace GlobalTheory

theorem localSpec_fac_of_closedPoint_mem_range (S : Type) [CommRing S] [IsLocalRing S] (X : Scheme.{0})
    (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (yb : Sp S ⟶ X) (hξ : IsOpenImmersion ξ)
    (hc : yb (IsLocalRing.closedPoint S) ∈ Set.range ξ) : ∃ φ : R →+* S, spMap φ ≫ ξ = yb := by
  have hrange : Set.range yb ⊆ Set.range ξ := by
    rintro _ ⟨x, rfl⟩
    have hsp : x ⤳ IsLocalRing.closedPoint S := IsLocalRing.specializes_closedPoint x
    exact (hsp.map yb.base.hom.continuous).mem_open ξ.isOpenEmbedding.isOpen_range hc
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ξ yb hrange)).hom, ?_⟩
  show Spec.map (Spec.preimage _) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

example : ∀ (S : Type) [CommRing S] [IsLocalRing S] (X : Scheme.{0}) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (yb : Sp S ⟶ X), IsOpenImmersion ξ → yb (IsLocalRing.closedPoint S) ∈ Set.range ξ → ∃ φ : R →+* S, spMap φ ≫ ξ = yb := @localSpec_fac_of_closedPoint_mem_range

end GlobalTheory
