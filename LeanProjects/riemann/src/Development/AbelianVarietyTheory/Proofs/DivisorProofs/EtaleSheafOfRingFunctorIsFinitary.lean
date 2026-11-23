import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitaryOfLocallyBijectiveFromFilteredFunctorStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in

theorem finite_etale_family {A : CommRingCat.{0}} (P : ∀ B : CommRingCat.{0}, (A ⟶ B) → Prop)
    (h : ∀ p : Spec A, ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (v : Spec B), g.hom.Etale ∧ Spec.map g v = p ∧ P B g) :
    ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i),
      (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, P (B i) (g i) := by
  choose B g v he hv hP using h
  have ho : ∀ p, IsOpen (Set.range (Spec.map (g p))) := fun p => by
    have : Etale (Spec.map (g p)) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 (he p)
    exact (Spec.map (g p)).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun p => Set.range (Spec.map (g p))) ho
    (fun p _ => Set.mem_iUnion.2 ⟨p, v p, hv p⟩)
  refine ⟨s, inferInstance, fun i => B i, fun i => g i, fun i => he i, fun p => ?_, fun i => hP i⟩
  obtain ⟨i, hi, w, hw⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ p))
  exact ⟨⟨i, hi⟩, w, hw⟩

set_option backward.isDefEq.respectTransparency false in

noncomputable def ofRingsUnit (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) :
    M ⟶ onRings (ofRings R M) where
  app A := M.map (Scheme.ΓSpecIso A).inv ≫ (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op (Spec A))
  naturality A B f := by
    have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality (Spec.map f).op
    rw [← Category.assoc, ← M.map_comp, Scheme.ΓSpecIso_inv_naturality, M.map_comp, Category.assoc, Category.assoc]
    congr 1

set_option backward.isDefEq.respectTransparency false in

theorem etale_affine_ring {A : CommRingCat.{0}} {V : Scheme.{0}} [IsAffine V] (j : V ⟶ Spec A) [Etale j] (v : V) :
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (k : Spec B ⟶ V) (w : Spec B), g.hom.Etale ∧ Spec.map g = k ≫ j ∧ k w = v := by
  refine ⟨Γ(V, ⊤), Spec.preimage (V.isoSpec.inv ≫ j), V.isoSpec.inv, V.isoSpec.hom v, ?_, Spec.map_preimage _, ?_⟩
  · refine (HasRingHomProperty.Spec_iff (P := @Etale)).1 ?_
    rw [Spec.map_preimage]
    infer_instance
  · rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem ofRings_finitary : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), PreservesFilteredColimitsOfSize.{0, 0} M → Finitary (ofRings R M) := by
  intro R _ M hM
  refine GlobalTheory.T.finitary_of_locally_bijective_from_filtered_functor R M (ofRings R M) (ofRingsUnit R M) hM (fun A x => ?_) (fun A m hm => ?_)
  · obtain ⟨ι, hι, B, g, he, hc, hP⟩ := finite_etale_family (A := A)
      (fun B g => ∃ m : M.obj B, ((ofRingsUnit R M).app B).hom m = ((onRings (ofRings R M)).map g).hom x) (fun p => by
        obtain ⟨V, j, v, m, hV, hj, hv, hm⟩ := (ofRings_loc R M (Spec A)).1 x p
        obtain ⟨B, g, k, w, hg, hk, hw⟩ := etale_affine_ring j v
        refine ⟨B, g, w, hg, by rw [hk, Scheme.Hom.comp_apply, hw, hv],
          (M.map (k.appTop ≫ (Scheme.ΓSpecIso B).hom)).hom m, ?_⟩
        have h1 : (M.map (Scheme.ΓSpecIso B).inv).hom ((M.map (k.appTop ≫ (Scheme.ΓSpecIso B).hom)).hom m) =
            (M.map k.appTop).hom m := by
          rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← M.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        change ofRings.sec M (Spec B) ((M.map (Scheme.ΓSpecIso B).inv).hom _) = Sec.res (F := ofRings R M) (Spec.map g) x
        rw [h1, ← (ofRings_loc R M V).2.2 _ k m, hm, hk]
        simp [Sec.res])
    choose m hm using hP
    exact ⟨ι, hι, B, g, m, he, hc, hm⟩
  · refine finite_etale_family (A := A) (fun B g => (M.map g).hom m = 0) (fun p => ?_)
    obtain ⟨V, j, v, hV, hj, hv, h0⟩ := (ofRings_loc R M (Spec A)).2.1 ((M.map (Scheme.ΓSpecIso A).inv).hom m) hm p
    obtain ⟨B, g, k, w, hg, hk, hw⟩ := etale_affine_ring j v
    refine ⟨B, g, w, hg, by rw [hk, Scheme.Hom.comp_apply, hw, hv], ?_⟩
    have h1 : g = (Scheme.ΓSpecIso A).inv ≫ j.appTop ≫ k.appTop ≫ (Scheme.ΓSpecIso B).hom := by
      rw [← Category.assoc j.appTop, ← Scheme.Hom.comp_appTop, ← hk, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rw [h1, M.map_comp, M.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, h0, map_zero]

end GlobalTheory
