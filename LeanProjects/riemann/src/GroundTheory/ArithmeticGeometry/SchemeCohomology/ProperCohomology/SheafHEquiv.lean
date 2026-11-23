import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafHOver
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite Abelian TopologicalSpace AlgebraicGeometry

universe w' v u

noncomputable section

section Congr

variable {C D : Type v} [SmallCategory C] [SmallCategory D] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  {T : C} (hT : IsTerminal T)

abbrev sheafCongrAb : Sheaf J AddCommGrpCat.{v} ≌ Sheaf K AddCommGrpCat.{v} :=
  e.sheafCongr J K AddCommGrpCat.{v}

def sheafCongrSectionsIso :
    (sheafCongrAb J K e).inverse ⋙ (sheafSections J AddCommGrpCat.{v}).obj (op T) ≅
      (sheafSections K AddCommGrpCat.{v}).obj (op (e.functor.obj T)) :=
  Iso.refl _

def constantSheafCongrIso :
    constantSheaf J AddCommGrpCat.{v} ⋙ (sheafCongrAb J K e).functor ≅
      constantSheaf K AddCommGrpCat.{v} :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj J AddCommGrpCat.{v} hT).comp (sheafCongrAb J K e).toAdjunction).ofNatIsoRight
      (sheafCongrSectionsIso J K e))
    (constantSheafAdj K AddCommGrpCat.{v} (hT.isTerminalObj e.functor))

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]

instance sheafCongrAb_functor_additive : (sheafCongrAb J K e).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance sheafCongrAb_functor_preservesInjectiveObjects :
    (sheafCongrAb J K e).functor.PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafCongrAb J K e).symm.toAdjunction

def sheafHCongr [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] (G : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) :
    Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} ((sheafCongrAb J K e).functor.obj G) n :=
  (AddEquiv.ofBijective _ ((sheafCongrAb J K e).functor.mapExt_bijective_of_preservesInjectiveObjects
      _ G n)).trans
    (extAddEquivOfIsoLeft ((constantSheafCongrIso J K e hT).app _) _ n)

end Congr

section Scheme

variable {X : Scheme.{u}} (U : X.Opens)

instance isDenseSubsite_overEquivalence_inverse :
    U.overEquivalence.inverse.IsDenseSubsite (Opens.grothendieckTopology U.toScheme.toTopCat)
      ((Opens.grothendieckTopology X.toTopCat).over U) :=
  U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence

lemma overEquivalence_inverse_left (W : U.toScheme.Opens) :
    (U.overEquivalence.inverse.obj W).left = U.ι ''ᵁ W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

set_option maxHeartbeats 4000000 in

def restrictAbIso (F : X.Modules) :
    (sheafCongrAb ((Opens.grothendieckTopology X.toTopCat).over U)
      (Opens.grothendieckTopology U.toScheme.toTopCat) U.overEquivalence).functor.obj
      ((modulesAb F).over U) ≅ modulesAb (F.restrict U.ι) :=
  (SheafOfModules.toSheaf _).mapIso ((Scheme.Modules.overFunctorEquiv U).app F)

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology U.toScheme.toTopCat) AddCommGrpCat.{u})]

def cohomologyPresheafAddEquivRestrict (F : X.Modules) (n : ℕ) :
    (modulesAb F).H' n U ≃+ Sheaf.H.{w'} (modulesAb (F.restrict U.ι)) n :=
  (cohomologyPresheafOverAddEquivOfSmall _ U (modulesAb F) n).trans
    ((sheafHCongr ((Opens.grothendieckTopology X.toTopCat).over U)
      (Opens.grothendieckTopology U.toScheme.toTopCat) U.overEquivalence Over.mkIdTerminal
      ((modulesAb F).over U) n).trans
      ((Sheaf.functorH _ n).mapIso (restrictAbIso U F)).addCommGroupIsoToAddEquiv)

lemma subsingleton_H'_of_restrict (F : X.Modules) (n : ℕ)
    [h : Subsingleton (Sheaf.H.{w'} (modulesAb (F.restrict U.ι)) n)] :
    Subsingleton ((modulesAb F).H' n U) :=
  (cohomologyPresheafAddEquivRestrict.{w'} U F n).toEquiv.subsingleton

end Scheme

end

end GroundTheory.Arith.SchemeCoh
