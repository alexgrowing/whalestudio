import Mathlib
import GroundTheory.TateCohomology.AugmentationSES
set_option maxSynthPendingDepth 1

open CategoryTheory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (S : ShortComplex (Rep.{u} k G)) {Y : Rep.{u} k G} (β : Y ⟶ S.X₃)

def pullbackSubmodule : Submodule k (S.X₂.V × Y.V) :=
  LinearMap.ker (S.g.hom.toLinearMap ∘ₗ LinearMap.fst k S.X₂.V Y.V -
    β.hom.toLinearMap ∘ₗ LinearMap.snd k S.X₂.V Y.V)

variable {S β} in
theorem mem_pullbackSubmodule {p : S.X₂.V × Y.V} :
    p ∈ pullbackSubmodule S β ↔ S.g.hom p.1 = β.hom p.2 := by
  simp [pullbackSubmodule, sub_eq_zero]

theorem pullbackSubmodule_le_comap (g : G) :
    pullbackSubmodule S β ≤ (pullbackSubmodule S β).comap ((S.X₂.ρ.prod Y.ρ) g) := by
  intro p hp
  rw [Submodule.mem_comap, mem_pullbackSubmodule]
  rw [mem_pullbackSubmodule] at hp
  simp [Rep.hom_comm_apply, hp]

noncomputable abbrev pullbackRep : Rep.{u} k G :=
  Rep.subrepresentation (Rep.of (S.X₂.ρ.prod Y.ρ)) (pullbackSubmodule S β)
    (pullbackSubmodule_le_comap S β)

noncomputable def pullbackFst : pullbackRep S β ⟶ S.X₂ :=
  Rep.ofHom ⟨LinearMap.fst k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

noncomputable def pullbackSnd : pullbackRep S β ⟶ Y :=
  Rep.ofHom ⟨LinearMap.snd k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

@[simp] theorem pullbackFst_apply (p : pullbackRep S β) : (pullbackFst S β).hom p = p.1.1 := rfl

@[simp] theorem pullbackSnd_apply (p : pullbackRep S β) : (pullbackSnd S β).hom p = p.1.2 := rfl

theorem g_apply_f_apply (x : S.X₁) : S.g.hom (S.f.hom x) = 0 := by
  change (S.f ≫ S.g).hom x = 0
  rw [S.zero]
  rfl

noncomputable def pullbackιLinear : S.X₁.V →ₗ[k] pullbackSubmodule S β :=
  LinearMap.codRestrict (pullbackSubmodule S β)
    (LinearMap.prod S.f.hom.toLinearMap 0) fun x => by
      rw [mem_pullbackSubmodule]
      simp [g_apply_f_apply]

noncomputable def pullbackι : S.X₁ ⟶ pullbackRep S β :=
  Rep.ofHom ⟨pullbackιLinear S β, fun g => by
    refine LinearMap.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
    · simp [pullbackιLinear, Rep.hom_comm_apply]
    · simp [pullbackιLinear]⟩

@[simp] theorem pullbackι_apply_fst (x : S.X₁) : ((pullbackι S β).hom x).1.1 = S.f.hom x := rfl

@[simp] theorem pullbackι_apply_snd (x : S.X₁) : ((pullbackι S β).hom x).1.2 = 0 := rfl

theorem pullbackι_pullbackSnd : pullbackι S β ≫ pullbackSnd S β = 0 := by
  ext x
  rfl

noncomputable def pullbackSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (pullbackι S β) (pullbackSnd S β) (pullbackι_pullbackSnd S β)

@[simp] theorem pullbackSES_X₁ : (pullbackSES S β).X₁ = S.X₁ := rfl
@[simp] theorem pullbackSES_X₂ : (pullbackSES S β).X₂ = pullbackRep S β := rfl
@[simp] theorem pullbackSES_X₃ : (pullbackSES S β).X₃ = Y := rfl
@[simp] theorem pullbackSES_f : (pullbackSES S β).f = pullbackι S β := rfl
@[simp] theorem pullbackSES_g : (pullbackSES S β).g = pullbackSnd S β := rfl

variable {S} in

theorem pullbackSES_shortExact (hS : S.ShortExact) : (pullbackSES S β).ShortExact := by
  have hex := function_exact_of_shortExact hS
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  refine shortExact_of_linear ?_ ?_ ?_
  · intro a b hab
    exact hinj (congrArg (fun p : pullbackRep S β => p.1.1) hab)
  · intro y
    obtain ⟨x, hx⟩ := hsurj (β.hom y)
    exact ⟨⟨(x, y), mem_pullbackSubmodule.2 hx⟩, rfl⟩
  · intro p hp
    have hp2 : p.1.2 = 0 := hp
    have hg : S.g.hom p.1.1 = 0 := by
      rw [(mem_pullbackSubmodule.1 p.2), hp2, map_zero]
    obtain ⟨x, hx⟩ := (hex p.1.1).1 hg
    refine ⟨x, Subtype.ext (Prod.ext hx hp2.symm)⟩

noncomputable def pullbackSESHom : pullbackSES S β ⟶ S where
  τ₁ := 𝟙 S.X₁
  τ₂ := pullbackFst S β
  τ₃ := β
  comm₁₂ := by
    ext x
    rfl
  comm₂₃ := by
    ext p
    exact mem_pullbackSubmodule.1 p.2

@[simp] theorem pullbackSESHom_τ₁ : (pullbackSESHom S β).τ₁ = 𝟙 S.X₁ := rfl
@[simp] theorem pullbackSESHom_τ₂ : (pullbackSESHom S β).τ₂ = pullbackFst S β := rfl
@[simp] theorem pullbackSESHom_τ₃ : (pullbackSESHom S β).τ₃ = β := rfl

end GroundTheory.GroupCoh
