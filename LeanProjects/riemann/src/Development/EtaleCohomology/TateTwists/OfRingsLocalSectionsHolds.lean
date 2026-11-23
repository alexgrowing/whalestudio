import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.EtaleCohomology.TateTwists.OfRingsLocalSections

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.OfRingsLoc
variable {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))

instance ls : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

instance li : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

omit [CommRing R] in
theorem ι_comp_apply {X U : Scheme.{0}} (f : X ⟶ U) (W : X.Opens) (y : X) (h : y ∈ W) :
    (Scheme.Opens.ι W ≫ f) ⟨y, h⟩ = f y :=
  rfl

omit [CommRing R] in

theorem cov_pt {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ S.arrows j := by
  obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have : Scheme.JointlySurjective (Scheme.precoverage.{0} @Etale) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ := (𝒰.X i).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : IsAffine W := hW
  have : Etale (𝒰.f i) := 𝒰.mem₀.2 ⟨i⟩
  refine ⟨W, Scheme.Opens.ι W ≫ 𝒰.f i, ⟨y, hyW⟩, inferInstance, inferInstance, ?_, ?_⟩
  · exact (ι_comp_apply (𝒰.f i) W y hyW).trans hy
  · exact S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) (Scheme.Opens.ι W)
theorem loc_surj {U : Scheme.{0}} (x : Sec (ofRings R M) U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)),
      IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x := by
  obtain ⟨V, j, v, hV, hj, hv, hS⟩ := cov_pt _
    (Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (U := op U) x) u
  obtain ⟨t, ht⟩ := hS
  exact ⟨V, j, v, t, hV, hj, hv, ht⟩

theorem loc_inj {U : Scheme.{0}} (m : M.obj Γ(U, ⊤)) (hm : ofRings.sec M U m = 0) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
      IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0 := by
  have h0 : ConcreteCategory.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U)) m =
      ConcreteCategory.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U)) 0 := by
    rw [map_zero]; exact hm
  obtain ⟨V, j, v, hV, hj, hv, hS⟩ := cov_pt _
    (Presheaf.equalizerSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) m 0 h0) u
  refine ⟨V, j, v, hV, hj, hv, ?_⟩
  have h1 : ConcreteCategory.hom ((Scheme.Γ ⋙ M).map j.op) m =
      ConcreteCategory.hom ((Scheme.Γ ⋙ M).map j.op) 0 := hS
  rw [map_zero] at h1
  exact h1
end LateralTheory.EtaleFoundations.OfRingsLoc
