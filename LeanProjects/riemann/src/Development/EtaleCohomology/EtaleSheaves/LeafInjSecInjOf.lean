import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.InjectiveSections

abbrev MC (q : ℕ) := ModuleCat.{1} (ULift.{1} (ZMod q))

theorem sigma_const_mono (q : ℕ) {α : Type} {d d' : MC q} (f : d ⟶ d') [Mono f] :
    Mono (Limits.Sigma.map (fun _ : α => f)) := by
  have : Mono (Discrete.natTrans (fun (_ : Discrete α) => f) : Discrete.functor (fun _ : α => d) ⟶ Discrete.functor (fun _ : α => d')) :=
    @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ (fun _ => inferInstanceAs (Mono f))
  have : AB4OfSize.{0} (MC q) := AB4OfSize_shrink.{0, 1} (MC q)
  have : HasExactColimitsOfShape (Discrete α) (MC q) := AB4OfSize.ofShape α
  have : PreservesFiniteLimits (colim : (Discrete α ⥤ MC q) ⥤ MC q) := inferInstance
  exact (Functor.map_mono colim (Discrete.natTrans (fun (_ : Discrete α) => f) : Discrete.functor (fun _ : α => d) ⟶ Discrete.functor (fun _ : α => d')) : _)

instance evalLA_mono (q : ℕ) (U : Scheme.{0}) :
    (evaluationLeftAdjoint (MC q) (op U)).PreservesMonomorphisms where
  preserves {d d'} f _ := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ (fun t => ?_)
    change Mono (Limits.Sigma.desc (fun h : op U ⟶ t => f ≫ Sigma.ι (fun _ => d') h))
    have h : Limits.Sigma.desc (fun h : op U ⟶ t => f ≫ Sigma.ι (fun _ => d') h) = Limits.Sigma.map (fun _ => f) := by
      apply Limits.Sigma.hom_ext; intro j; rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_map]
    rw [h]
    exact sigma_const_mono q f

theorem eval_injective (q : ℕ) (M : Shv (ZMod q)) [Injective M] (U : Scheme.{0}) :
    Injective (M.obj.obj (op U)) := by
  have h1 : Injective ((sheafToPresheaf Scheme.etaleTopology.{0} (MC q)).obj M) :=
    Injective.injective_of_adjoint (sheafificationAdjunction Scheme.etaleTopology.{0} (MC q)) M
  have h2 : Injective M.obj := h1
  exact Injective.injective_of_adjoint (evaluationAdjunctionRight (MC q) (op U)) M.obj

end LateralTheory.E.InjectiveSections

open LateralTheory.E.InjectiveSections in
theorem LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj_of : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj := by
  intro q _ M _ U
  have h := eval_injective q M U
  exact Module.injective_module_of_injective_object (ULift.{1} (ZMod q)) (Sec M U)
