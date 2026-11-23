import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointFactorsOpenImmersion
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_point_factors_open_immersion : ∀ (S : Type) [CommRing S] [IsLocalRing S] (X : Scheme.{0}) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (yb : Sp S ⟶ X), IsOpenImmersion ξ → yb (IsLocalRing.closedPoint S) ∈ Set.range ξ → ∃ φ : R →+* S, spMap φ ≫ ξ = yb := by
  first | exact @GlobalTheory.localSpec_fac_of_closedPoint_mem_range | exact GlobalTheory.localSpec_fac_of_closedPoint_mem_range | (intros; apply GlobalTheory.localSpec_fac_of_closedPoint_mem_range <;> assumption)
