import Mathlib
import GroundTheory.TateCohomology.Induced
import GroundTheory.TateCohomology.InducedNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section ConnectingIso

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem isIso_δ_of_tateAcyclic {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h : TateAcyclic S.X₂) (n : ℤ) : IsIso (TateCohomology.δ hS n) := by
  have : Mono (TateCohomology.δ hS n) :=
    (TateCohomology.exact₃ hS n).mono_g ((h n).eq_of_src _ _)
  have : Epi (TateCohomology.δ hS n) :=
    (TateCohomology.exact₁ hS n).epi_f ((h (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end ConnectingIso

variable {k G : Type u} [CommRing k] [Group G]

section Coind

noncomputable abbrev toCoind (A : Rep.{u} k G) :
    A ⟶ coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) :=
  (resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.app A

theorem toCoind_hom_apply (A : Rep.{u} k G) (a : A) (x : G) :
    ((toCoind A).hom a).1 x = A.ρ x a := rfl

theorem toCoind_injective (A : Rep.{u} k G) : Function.Injective (toCoind A).hom := by
  intro a b hab
  have h : ((toCoind A).hom a).1 1 = ((toCoind A).hom b).1 1 := by rw [hab]
  rwa [toCoind_hom_apply, toCoind_hom_apply, map_one, Module.End.one_apply,
    Module.End.one_apply] at h

instance (A : Rep.{u} k G) : Mono (toCoind A) :=
  (Rep.mono_iff_injective _).2 (toCoind_injective A)

noncomputable def coindSES : Rep.{u} k G ⥤ ShortComplex (Rep.{u} k G) where
  obj A := ShortComplex.mk (toCoind A) (cokernel.π (toCoind A)) (cokernel.condition _)
  map {A B} f :=
    { τ₁ := f
      τ₂ := (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map f
      τ₃ := cokernel.map (toCoind A) (toCoind B) f _
        ((resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.naturality f).symm
      comm₁₂ := (resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.naturality f
      comm₂₃ := by simp }
  map_id A := by
    refine ShortComplex.hom_ext _ _ rfl ?_ ?_
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_id A
    · have h : coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (𝟙 A)) = 𝟙 _ :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_id A
      exact coequalizer.hom_ext (by simp [h])
  map_comp f g := by
    refine ShortComplex.hom_ext _ _ rfl ?_ ?_
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_comp f g
    · have h : coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (f ≫ g)) =
          coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype f) ≫
            coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype g) :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_comp f g
      exact coequalizer.hom_ext (by simp [h])

@[simp] theorem coindSES_obj_X₁ (A : Rep.{u} k G) : (coindSES.obj A).X₁ = A := rfl

@[simp] theorem coindSES_obj_X₂ (A : Rep.{u} k G) :
    (coindSES.obj A).X₂ = coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) := rfl

@[simp] theorem coindSES_obj_f (A : Rep.{u} k G) : (coindSES.obj A).f = toCoind A := rfl

@[simp] theorem coindSES_map_τ₁ {A B : Rep.{u} k G} (f : A ⟶ B) : (coindSES.map f).τ₁ = f := rfl

theorem coindSES_shortExact (A : Rep.{u} k G) : (coindSES.obj A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (toCoind A))
  mono_f := inferInstanceAs (Mono (toCoind A))
  epi_g := coequalizer.π_epi

noncomputable abbrev coindShift (A : Rep.{u} k G) : Rep.{u} k G := (coindSES.obj A).X₃

variable [Fintype G]

theorem tateAcyclic_coindSES_X₂ (A : Rep.{u} k G) : TateAcyclic (coindSES.obj A).X₂ :=
  tateAcyclic_coind_bot _

noncomputable def coindShiftIso (A : Rep.{u} k G) (n : ℤ) :
    tateCohomology (coindShift A) n ≅ tateCohomology A (n + 1) :=
  @asIso _ _ _ _ (TateCohomology.δ (coindSES_shortExact A) n)
    (isIso_δ_of_tateAcyclic (coindSES_shortExact A) (tateAcyclic_coindSES_X₂ A) n)

theorem isIso_δ_coindSES (A : Rep.{u} k G) (n : ℤ) :
    IsIso (TateCohomology.δ (coindSES_shortExact A) n) :=
  isIso_δ_of_tateAcyclic _ (tateAcyclic_coindSES_X₂ A) n

end Coind

section Ind

noncomputable abbrev fromInd (A : Rep.{u} k G) :
    ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) ⟶ A :=
  (indResAdjunction k (⊥ : Subgroup G).subtype).counit.app A

theorem fromInd_surjective (A : Rep.{u} k G) : Function.Surjective (fromInd A).hom := by
  intro a
  refine ⟨Representation.IndV.mk _ _ 1 a, ?_⟩
  change ((indResHomEquiv _ _ _).symm (𝟙 _)).hom _ = a
  simp

instance (A : Rep.{u} k G) : Epi (fromInd A) :=
  (Rep.epi_iff_surjective _).2 (fromInd_surjective A)

noncomputable def indSES : Rep.{u} k G ⥤ ShortComplex (Rep.{u} k G) where
  obj A := ShortComplex.mk (kernel.ι (fromInd A)) (fromInd A) (kernel.condition _)
  map {A B} f :=
    { τ₁ := kernel.map (fromInd A) (fromInd B)
        ((resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map f) f
        ((indResAdjunction k (⊥ : Subgroup G).subtype).counit.naturality f).symm
      τ₂ := (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map f
      τ₃ := f
      comm₁₂ := by simp
      comm₂₃ := (indResAdjunction k (⊥ : Subgroup G).subtype).counit.naturality f }
  map_id A := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
    · have h : indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (𝟙 A)) = 𝟙 _ :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_id A
      exact equalizer.hom_ext (by simp [h])
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_id A
  map_comp f g := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
    · have h : indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (f ≫ g)) =
          indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype f) ≫
            indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype g) :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_comp f g
      exact equalizer.hom_ext (by simp [h])
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_comp f g

@[simp] theorem indSES_obj_X₂ (A : Rep.{u} k G) :
    (indSES.obj A).X₂ = ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) := rfl

@[simp] theorem indSES_obj_X₃ (A : Rep.{u} k G) : (indSES.obj A).X₃ = A := rfl

@[simp] theorem indSES_obj_g (A : Rep.{u} k G) : (indSES.obj A).g = fromInd A := rfl

@[simp] theorem indSES_map_τ₃ {A B : Rep.{u} k G} (f : A ⟶ B) : (indSES.map f).τ₃ = f := rfl

theorem indSES_shortExact (A : Rep.{u} k G) : (indSES.obj A).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (fromInd A))
  mono_f := equalizer.ι_mono
  epi_g := inferInstanceAs (Epi (fromInd A))

noncomputable abbrev indShift (A : Rep.{u} k G) : Rep.{u} k G := (indSES.obj A).X₁

variable [Fintype G]

theorem tateAcyclic_indSES_X₂ (A : Rep.{u} k G) : TateAcyclic (indSES.obj A).X₂ :=
  tateAcyclic_ind_bot _

noncomputable def indShiftIso (A : Rep.{u} k G) (n : ℤ) :
    tateCohomology A n ≅ tateCohomology (indShift A) (n + 1) :=
  @asIso _ _ _ _ (TateCohomology.δ (indSES_shortExact A) n)
    (isIso_δ_of_tateAcyclic (indSES_shortExact A) (tateAcyclic_indSES_X₂ A) n)

theorem isIso_δ_indSES (A : Rep.{u} k G) (n : ℤ) :
    IsIso (TateCohomology.δ (indSES_shortExact A) n) :=
  isIso_δ_of_tateAcyclic _ (tateAcyclic_indSES_X₂ A) n

end Ind

end GroundTheory.GroupCoh
