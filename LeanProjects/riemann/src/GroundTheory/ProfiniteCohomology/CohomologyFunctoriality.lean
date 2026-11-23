import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]

section Discrete

theorem IsDiscreteRep.res {φ : H →* G} (hφ : Continuous φ) (A : Rep.{u} k G) [IsDiscreteRep A] :
    IsDiscreteRep (Rep.res φ A) :=
  ⟨fun a => by
    have h : (stabilizer (Rep.res φ A).ρ a : Set H) = φ ⁻¹' (stabilizer A.ρ a : Set G) := rfl
    rw [h]
    exact (GroundTheory.ProfCoh.isOpen_stabilizer A a).preimage hφ⟩

theorem continuous_subgroup_subtype (S : Subgroup G) : Continuous S.subtype :=
  continuous_subtype_val

theorem continuous_quotientGroup_mk' (N : Subgroup G) [N.Normal] :
    Continuous (QuotientGroup.mk' N) :=
  QuotientGroup.continuous_mk

instance isDiscreteRep_res_subtype (A : Rep.{u} k G) [IsDiscreteRep A] (S : Subgroup G) :
    IsDiscreteRep (Rep.res S.subtype A) :=
  IsDiscreteRep.res (continuous_subgroup_subtype S) A

instance isDiscreteRep_quotientToInvariants_of_normal (A : Rep.{u} k G) [IsDiscreteRep A]
    (N : Subgroup G) [N.Normal] : IsDiscreteRep (A.quotientToInvariants N) :=
  ⟨fun a => by
    rw [← (QuotientGroup.isQuotientMap_mk N).isOpen_preimage]
    have h : (QuotientGroup.mk ⁻¹' (stabilizer (A.quotientToInvariants N).ρ a : Set (G ⧸ N))) =
        (stabilizer A.ρ a.1 : Set G) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, mem_stabilizer]
      rw [Subtype.ext_iff]
      rfl
    rw [h]
    exact isOpen_stabilizer A a.1⟩

end Discrete

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup K]

section Cochains

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in

theorem isLocallyConstant_cochainsMapAlong {A : Rep.{u} k G} {B : Rep.{u} k H} {φ : H →* G}
    (hφ : Continuous φ) (f : Rep.res φ A ⟶ B) {n : ℕ} {x : (Fin n → G) → A}
    (hx : IsLocallyConstant x) :
    IsLocallyConstant (((groupCohomology.cochainsMap φ f).f n).hom x) := by
  have hc : Continuous fun h : Fin n → H => (⇑φ ∘ h) :=
    continuous_pi fun i => hφ.comp (continuous_apply i)
  exact (hx.comp_continuous hc).comp _

noncomputable def cochainsMapAlong {A : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A]
    [IsDiscreteRep B] (φ : H →* G) (hφ : Continuous φ) (f : Rep.res φ A ⟶ B) :
    cochainsComplex A ⟶ cochainsComplex B where
  f n := ModuleCat.ofHom (((groupCohomology.cochainsMap φ f).f n).hom.restrict
    fun _ hx => isLocallyConstant_cochainsMapAlong hφ f hx)
  comm' i j (hij : i + 1 = j) := by
    subst hij
    rw [cochainsComplex_d, cochainsComplex_d]
    ext x : 2
    apply Subtype.ext
    have h := (groupCohomology.cochainsMap φ f).comm i (i + 1)
    rw [groupCohomology.inhomogeneousCochains.d_def,
      groupCohomology.inhomogeneousCochains.d_def] at h
    exact congrArg (fun ψ => ψ.hom x.1) h

variable {A : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A] [IsDiscreteRep B]
  (φ : H →* G) (hφ : Continuous φ) (f : Rep.res φ A ⟶ B)

theorem cochainsComplexι_cochainsMapAlong_apply (n : ℕ) (x : (cochainsComplex A).X n) :
    ((cochainsComplexι B).f n).hom (((cochainsMapAlong φ hφ f).f n).hom x) =
      fun h => f.hom (((cochainsComplexι A).f n).hom x (⇑φ ∘ h)) :=
  rfl

@[reassoc]
theorem cochainsMapAlong_comp_cochainsComplexι :
    cochainsMapAlong φ hφ f ≫ cochainsComplexι B =
      cochainsComplexι A ≫ groupCohomology.cochainsMap φ f := by
  ext n x : 3
  rfl

@[simp]
theorem cochainsMapAlong_id : cochainsMapAlong (MonoidHom.id G) continuous_id (𝟙 A) = 𝟙 _ := by
  ext n x : 3
  rfl

@[reassoc]
theorem cochainsMapAlong_comp {C : Rep.{u} k K} [IsDiscreteRep C] (ψ : K →* H) (hψ : Continuous ψ)
    (g : Rep.res ψ B ⟶ C) :
    cochainsMapAlong (φ.comp ψ) (hφ.comp hψ) ((Rep.resFunctor ψ).map f ≫ g) =
      cochainsMapAlong φ hφ f ≫ cochainsMapAlong ψ hψ g := by
  ext n x : 3
  rfl

@[reassoc]
theorem cochainsMapAlong_id_comp {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    [IsDiscreteRep C] (f : A ⟶ B) (g : B ⟶ C) :
    cochainsMapAlong (MonoidHom.id G) continuous_id (f ≫ g) =
      cochainsMapAlong (MonoidHom.id G) continuous_id f ≫
        cochainsMapAlong (MonoidHom.id G) continuous_id g := by
  ext n x : 3
  rfl

@[simp]
theorem cochainsMapAlong_zero : cochainsMapAlong φ hφ (0 : Rep.res φ A ⟶ B) = 0 := by
  ext n x : 3
  rfl

end Cochains

section Cohomology

variable {A : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A] [IsDiscreteRep B]
  (φ : H →* G) (hφ : Continuous φ) (f : Rep.res φ A ⟶ B)

noncomputable abbrev cocyclesMapAlong (n : ℕ) : cocycles A n ⟶ cocycles B n :=
  HomologicalComplex.cyclesMap (cochainsMapAlong φ hφ f) n

noncomputable def cohomologyMapAlong (n : ℕ) : cohomology A n ⟶ cohomology B n :=
  HomologicalComplex.homologyMap (cochainsMapAlong φ hφ f) n

@[reassoc, elementwise]
theorem cohomologyπ_cohomologyMapAlong (n : ℕ) :
    cohomologyπ A n ≫ cohomologyMapAlong φ hφ f n = cocyclesMapAlong φ hφ f n ≫ cohomologyπ B n := by
  simp [cohomologyMapAlong, cocyclesMapAlong, cohomologyπ, cohomology]

@[simp]
theorem cohomologyMapAlong_id (n : ℕ) :
    cohomologyMapAlong (MonoidHom.id G) continuous_id (𝟙 A) n = 𝟙 _ := by
  rw [cohomologyMapAlong, cochainsMapAlong_id]
  exact HomologicalComplex.homologyMap_id _ _

@[reassoc]
theorem cohomologyMapAlong_comp {C : Rep.{u} k K} [IsDiscreteRep C] (ψ : K →* H) (hψ : Continuous ψ)
    (g : Rep.res ψ B ⟶ C) (n : ℕ) :
    cohomologyMapAlong (φ.comp ψ) (hφ.comp hψ) ((Rep.resFunctor ψ).map f ≫ g) n =
      cohomologyMapAlong φ hφ f n ≫ cohomologyMapAlong ψ hψ g n := by
  rw [cohomologyMapAlong, cochainsMapAlong_comp, HomologicalComplex.homologyMap_comp]
  rfl

@[reassoc]
theorem cohomologyMapAlong_id_comp {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    [IsDiscreteRep C] (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    cohomologyMapAlong (MonoidHom.id G) continuous_id (f ≫ g) n =
      cohomologyMapAlong (MonoidHom.id G) continuous_id f n ≫
        cohomologyMapAlong (MonoidHom.id G) continuous_id g n := by
  rw [cohomologyMapAlong, cochainsMapAlong_id_comp, HomologicalComplex.homologyMap_comp]
  rfl

@[reassoc]
theorem cohomologyMapAlong_comp_homologyMap_cochainsComplexι (n : ℕ) :
    cohomologyMapAlong φ hφ f n ≫ (HomologicalComplex.homologyMap (cochainsComplexι B) n :
        cohomology B n ⟶ groupCohomology B n) =
      (HomologicalComplex.homologyMap (cochainsComplexι A) n :
        cohomology A n ⟶ groupCohomology A n) ≫ groupCohomology.map φ f n := by
  have h := congrArg (fun ψ => HomologicalComplex.homologyMap ψ n)
    (cochainsMapAlong_comp_cochainsComplexι φ hφ f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

end Cohomology

section Restriction

variable (A : Rep.{u} k G) [IsDiscreteRep A]

noncomputable def cohomologyRes (S : Subgroup G) (n : ℕ) :
    cohomology A n ⟶ cohomology (Rep.res S.subtype A) n :=
  cohomologyMapAlong S.subtype (continuous_subgroup_subtype S) (𝟙 _) n

theorem cohomologyRes_eq (S : Subgroup G) (n : ℕ) :
    cohomologyRes A S n = cohomologyMapAlong S.subtype (continuous_subgroup_subtype S) (𝟙 _) n :=
  rfl

@[reassoc]
theorem cohomologyRes_naturality {A' : Rep.{u} k G} [IsDiscreteRep A'] (g : A ⟶ A')
    (S : Subgroup G) (n : ℕ) :
    cohomologyMapAlong (MonoidHom.id G) continuous_id g n ≫ cohomologyRes A' S n =
      cohomologyRes A S n ≫
        cohomologyMapAlong (MonoidHom.id S) continuous_id ((Rep.resFunctor S.subtype).map g) n := by
  rw [cohomologyRes, cohomologyRes, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  rfl

@[reassoc]
theorem cohomologyRes_comp_homologyMap_cochainsComplexι (S : Subgroup G) (n : ℕ) :
    cohomologyRes A S n ≫
      (HomologicalComplex.homologyMap (cochainsComplexι (Rep.res S.subtype A)) n :
        cohomology (Rep.res S.subtype A) n ⟶ groupCohomology (Rep.res S.subtype A) n) =
      (HomologicalComplex.homologyMap (cochainsComplexι A) n :
        cohomology A n ⟶ groupCohomology A n) ≫ groupCohomology.map S.subtype (𝟙 _) n :=
  cohomologyMapAlong_comp_homologyMap_cochainsComplexι _ _ _ n

end Restriction

section Inflation

variable (A : Rep.{u} k G) [IsDiscreteRep A]

noncomputable def cohomologyInfl (N : Subgroup G) [N.Normal] (n : ℕ) :
    cohomology (A.quotientToInvariants N) n ⟶ cohomology A n :=
  cohomologyMapAlong (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N)
    (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) n

theorem cohomologyInfl_eq (N : Subgroup G) [N.Normal] (n : ℕ) :
    cohomologyInfl A N n = cohomologyMapAlong (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) n :=
  rfl

@[reassoc]
theorem cohomologyInfl_comp_homologyMap_cochainsComplexι (N : Subgroup G) [N.Normal] (n : ℕ) :
    cohomologyInfl A N n ≫ (HomologicalComplex.homologyMap (cochainsComplexι A) n :
        cohomology A n ⟶ groupCohomology A n) =
      (HomologicalComplex.homologyMap (cochainsComplexι (A.quotientToInvariants N)) n :
        cohomology (A.quotientToInvariants N) n ⟶ groupCohomology (A.quotientToInvariants N) n) ≫
        groupCohomology.map (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) n :=
  cohomologyMapAlong_comp_homologyMap_cochainsComplexι _ _ _ n

end Inflation

end GroundTheory.ProfCoh
