import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def ForgetInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) [Injective F] (S : Scheme.{0}),
  ∃ h : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((Over.forget S).op ⋙ F.obj),
    Injective (⟨_, h⟩ : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R)))

theorem pushPullback_inj {R : Type} [CommRing R] {X S : Scheme.{0}} (p : X ⟶ S)
    (G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R))) [Injective G] :
    Injective (((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G) := by
  have adj := (Over.mapPullbackAdj p).sheafPushforwardContinuous (E := ModuleCat.{1} (ULift.{1} R))
    (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)
  have : ((Over.map p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)).PreservesMonomorphisms := inferInstance
  exact Injective.injective_of_adjoint adj G

theorem InjSlice_of (hF : ForgetInj) : InjSlice := by
  intro R _ F _ X S p
  obtain ⟨hX, iX⟩ := hF R F X
  refine ⟨?_, hF R F S⟩
  let G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R)) := ⟨_, hX⟩
  exact ⟨(((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G).2, pushPullback_inj p G⟩

end LateralTheory.KummerTheory
