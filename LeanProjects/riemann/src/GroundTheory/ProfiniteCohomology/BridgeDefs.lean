import Mathlib
import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G]

abbrev underlyingRep (X : TopRep.{u} k G) : Rep.{u} k G :=
  Rep.of X.ρ.toRepresentation

@[simp]
theorem underlyingRep_ρ_apply (X : TopRep.{u} k G) (g : G) (x : X) :
    (underlyingRep X).ρ g x = X.ρ g x :=
  rfl

section Discrete

variable [DiscreteTopology k]

def discreteTopRep (A : Rep.{u} k G) : TopRep.{u} k G :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  haveI : ContinuousSMul k A := ⟨continuous_of_discreteTopology⟩
  haveI : IsTopologicalAddGroup A := ⟨⟩
  TopRep.of (X := A) <| ContRepresentation.ofMonoidHom
    { toFun g := { toLinearMap := A.ρ g, cont := continuous_of_discreteTopology }
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }

instance (A : Rep.{u} k G) : DiscreteTopology (discreteTopRep A) :=
  ⟨rfl⟩

variable [TopologicalSpace G]

instance (A : Rep.{u} k G) [IsDiscreteRep A] : IsDiscreteRep (underlyingRep (discreteTopRep A)) :=
  ‹IsDiscreteRep A›

end Discrete

end GroundTheory.ProfCoh
