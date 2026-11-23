import Development.EtaleCohomology.TateTwists.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwResSecInj

theorem sigma_map_mono (R : Type) [CommRing R] (ι : Type) {X Y : ModuleCat.{1} (ULift.{1} R)} (f : X ⟶ Y) [Mono f] :
    Mono (Limits.Sigma.map (fun (_ : ι) => f)) := by
  let α : Discrete.functor (fun (_ : ι) => X) ⟶ Discrete.functor (fun _ => Y) := Discrete.natTrans (fun _ => f)
  have : ∀ j, Mono (α.app j) := fun j => by
    change Mono f; infer_instance
  have h1 : Mono α := NatTrans.mono_of_mono_app _
  exact (colim : (Discrete ι ⥤ ModuleCat.{1} (ULift.{1} R)) ⥤ _).map_mono α

instance evLA_mono (R : Type) [CommRing R] (U : Scheme.{0}) :
    (evaluationLeftAdjoint (ModuleCat.{1} (ULift.{1} R)) (op U)).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    have hm : ∀ c, Mono (((evaluationLeftAdjoint (ModuleCat.{1} (ULift.{1} R)) (op U)).map f).app c) := by
      intro c
      rw [evaluationLeftAdjoint_map_app]
      have e : (Limits.Sigma.desc fun h => f ≫ Sigma.ι (fun _ => Y) h) = Limits.Sigma.map (fun (_ : op U ⟶ c) => f) := by
        ext; simp
      rw [e]; exact sigma_map_mono R _ f
    exact NatTrans.mono_of_mono_app _

end LateralTheory.EtaleFoundations.TwResSecInj

open LateralTheory.EtaleFoundations.TwResSecInj in
theorem LateralTheory.EtaleFoundations.etale_injective_sheaf_sections_injective_holds : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective := by
  intro R _ M _ U
  have adj := (evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} R)) (op U)).comp
    (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))
  have hI := Injective.injective_of_adjoint adj M
  exact Module.injective_module_of_injective_object (inj := hI) _ _
