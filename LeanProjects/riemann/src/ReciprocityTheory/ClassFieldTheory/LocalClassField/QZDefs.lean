import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.ContinuousContractNth

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

def trivRep (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] : TRep ℤ G :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  { V := A
    rho := 1
    cont := continuous_snd }

scoped instance (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] :
    DiscreteTopology (trivRep G A).V := ⟨rfl⟩

def trivMap (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Type} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) : Pair (trivRep G A) (trivRep G B) :=
  Pair.ofMap (M := trivRep G A) (M' := trivRep G B) f.toIntLinearMap continuous_of_discreteTopology
    fun _ _ => rfl

def charGrp (G : Type) [Group G] [TopologicalSpace G] : AddSubgroup (Additive G →+ QZ) where
  carrier := {χ | IsLocallyConstant fun g : G => χ (Additive.ofMul g)}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' := fun ha hb => IsLocallyConstant.add ha hb
  neg_mem' := fun ha => IsLocallyConstant.neg ha

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
