import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsContinuousForgetForget
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyEquivEllAdicCohomology

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Rel

set_option backward.isDefEq.respectTransparency.types false in

theorem pull_preservesFiniteLimits (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : Y ⟶ X) :
    PreservesFiniteLimits (pull R f) := by
  have : AB5OfSize.{0, 1} (ModuleCat.{1} (ULift.{1} R)) := AB5OfSize_of_univLE.{0, 1, 1, 1} _
  have hf (U : Y.Etaleᵒᵖ) : IsFiltered (CostructuredArrow (bc f).op U) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (bc f) (unop U))
  have : PreservesFiniteLimits ((bc f).op.lan : (_ ⥤ _ ⥤ ModuleCat.{1} (ULift.{1} R))) :=
    GlobalTheory.Et.Small.lan_preservesFiniteLimits _ _ (fun U => by have := hf U; infer_instance)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits (bc f) _ _ _

end GlobalTheory.EtC.Rel
