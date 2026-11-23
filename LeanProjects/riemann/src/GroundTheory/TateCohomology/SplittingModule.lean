import Mathlib
import GroundTheory.TateCohomology.PullbackExtension
import GroundTheory.TateCohomology.AugTrivial
import GroundTheory.TateCohomology.DeltaMap
import GroundTheory.TateCohomology.DimensionShift
import GroundTheory.TateCohomology.TateConnecting
set_option maxSynthPendingDepth 1

open CategoryTheory Limits groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

section Construction

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (M : Rep.{u} k G)
  (u : groupCohomology M 2)

theorem isZero_groupCohomology_coind_two : IsZero (groupCohomology (coindSES.obj M).X₂ 2) :=
  ((tateAcyclic_coindSES_X₂ M) 2).of_iso (tateIsoH _ 2 2 rfl).symm

theorem exists_cocycle_δ_eq : ∃ f : cocycles₁ (coindSES.obj M).X₃,
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ f) = u := by
  have : Epi (δ (coindSES_shortExact M) 1 2 rfl) :=
    epi_δ_of_isZero (coindSES_shortExact M) 1 (isZero_groupCohomology_coind_two M)
  obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective _).1 this u
  obtain ⟨f, rfl⟩ := (ModuleCat.epi_iff_surjective (H1π _)).1 inferInstance v
  exact ⟨f, hv⟩

noncomputable def splittingCocycle : cocycles₁ (coindSES.obj M).X₃ :=
  (exists_cocycle_δ_eq M u).choose

theorem δ_splittingCocycle :
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ (splittingCocycle M u)) = u :=
  (exists_cocycle_δ_eq M u).choose_spec

noncomputable def splittingSES : ShortComplex (Rep.{u} k G) :=
  pullbackSES (coindSES.obj M) (cocycleHom (splittingCocycle M u))

theorem splittingSES_shortExact : (splittingSES M u).ShortExact :=
  pullbackSES_shortExact _ (coindSES_shortExact M)

noncomputable abbrev splittingModule : Rep.{u} k G := (splittingSES M u).X₂

omit [Fintype G] in

theorem map_H1π_augCocycle {H : Type u} [Group H] (φ : H →* G) {A : Rep.{u} k G}
    (f : cocycles₁ A) :
    map (A := res φ (augIdeal k G)) (B := res φ A) (MonoidHom.id H)
      ((resFunctor φ).map (cocycleHom f)) 1 (H1π _ (augCocycle k φ)) =
    map φ (𝟙 (res φ A)) 1 (H1π A f) := by
  rw [H1π_comp_map_apply, H1π_comp_map_apply]
  congr 1
  apply cocycles₁_ext
  intro h
  exact cocycleHom_augIdealSubOne f (φ h)

noncomputable def splittingSESResHom {H : Type u} [Group H] (φ : H →* G) :
    (splittingSES M u).map (resFunctor φ) ⟶ (coindSES.obj M).map (resFunctor φ) where
  τ₁ := 𝟙 _
  τ₂ := (resFunctor φ).map (pullbackFst _ (cocycleHom (splittingCocycle M u)))
  τ₃ := (resFunctor φ).map (cocycleHom (splittingCocycle M u))
  comm₁₂ := by
    ext x
    rfl
  comm₂₃ := by
    ext p
    exact mem_pullbackSubmodule.1 p.2

theorem δ_splittingSES_res_δ₀ {H : Type u} [Group H] (φ : H →* G) :
    δ ((shortExact_res φ).2 (splittingSES_shortExact M u)) 1 2 rfl
      (δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ))) =
    map φ (𝟙 (res φ M)) 2 u := by
  rw [δ₀_augTrivSES_res]
  have hN := groupCohomology.δ_naturality ((shortExact_res φ).2 (splittingSES_shortExact M u))
    ((shortExact_res φ).2 (coindSES_shortExact M)) (splittingSESResHom M u φ) 1 2 rfl
  have e : (map (MonoidHom.id H) (𝟙 (res φ M)) 2).hom
      (δ ((shortExact_res φ).2 (splittingSES_shortExact M u)) 1 2 rfl
        (H1π (res φ (augIdeal k G)) (augCocycle k φ))) =
      (δ ((shortExact_res φ).2 (coindSES_shortExact M)) 1 2 rfl).hom
        ((map (A := res φ (augIdeal k G)) (B := res φ (coindSES.obj M).X₃) (MonoidHom.id H)
          ((resFunctor φ).map (cocycleHom (splittingCocycle M u))) 1).hom
          (H1π _ (augCocycle k φ))) :=
    congr(($hN).hom (H1π _ (augCocycle k φ)))
  have hid : ∀ y, (map (A := res φ M) (B := res φ M) (MonoidHom.id H) (𝟙 (res φ M)) 2).hom y =
      y := fun y => by
    rw [groupCohomology.map_id]
    rfl
  have hR := congr(($(δ_comp_map_res φ (coindSES_shortExact M) 1 2 rfl)).hom
    (H1π _ (splittingCocycle M u)))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hR
  have hR' : (map φ (𝟙 (res φ M)) 2).hom u =
      (δ ((shortExact_res φ).2 (coindSES_shortExact M)) 1 2 rfl).hom
        ((map φ (𝟙 (res φ (coindSES.obj M).X₃)) 1).hom (H1π _ (splittingCocycle M u))) := by
    conv_lhs => rw [← δ_splittingCocycle M u]
    exact hR
  refine (hid _).symm.trans (e.trans ?_)
  rw [map_H1π_augCocycle φ (splittingCocycle M u)]
  exact hR'.symm

end Construction

end GroundTheory.GroupCoh
