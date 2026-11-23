import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.ConjAction
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.Shapiro
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section Nsmul

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem bijective_nsmul_cohomology (B : Rep.{u} k Γ) [IsDiscreteRep B] (m : ℕ)
    (hB : Function.Bijective fun b : B => m • b) (n : ℕ) :
    Function.Bijective fun x : cohomology B n => m • x := by
  let L : B →ₗ[k] B := m • LinearMap.id
  let e : B ≃ₗ[k] B := LinearEquiv.ofBijective L hB
  have he : ∀ b : B, e b = m • b := fun _ => rfl
  let φ : B ⟶ B := Rep.ofHom ⟨e.symm.toLinearMap, fun g => by
    ext b
    apply e.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [he, ← map_nsmul, ← he, LinearEquiv.apply_symm_apply]⟩
  have h1 : (m • 𝟙 B) ≫ φ = 𝟙 B := by
    ext b
    change e.symm (m • b) = b
    rw [← he, LinearEquiv.symm_apply_apply]
  have h2 : φ ≫ (m • 𝟙 B) = 𝟙 B := by
    ext b
    change m • e.symm b = b
    rw [← he, LinearEquiv.apply_symm_apply]
  have hf : (fun x : cohomology B n => m • x) = (cohomologyMap (m • 𝟙 B) n).hom := by
    funext x
    rw [cohomologyMap_nsmul_id_apply]
  rw [hf]
  refine Function.bijective_iff_has_inverse.2 ⟨(cohomologyMap φ n).hom, fun x => ?_, fun x => ?_⟩
  · rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, h1, cohomologyMap_id]
    rfl
  · rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, h2, cohomologyMap_id]
    rfl

end Nsmul

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G) [(U : Subgroup G).Normal] (A : Rep.{u} k G)
  [IsDiscreteRep A]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section ResCores

noncomputable def coindTraceTermMor (c : G ⧸ (U : Subgroup G)) :
    Rep.res (U : Subgroup G).subtype
        (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) ⟶
      Rep.res (U : Subgroup G).subtype A :=
  Rep.ofHom ⟨coindTraceTerm (U : Subgroup G) A c, fun u => by
    ext f
    induction c using QuotientGroup.induction_on with
    | H x =>
      change coindTraceTerm (U : Subgroup G) A (x : G ⧸ (U : Subgroup G))
          ((Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)).ρ u f) =
        A.ρ u (coindTraceTerm (U : Subgroup G) A (x : G ⧸ (U : Subgroup G)) f)
      rw [coindTraceTerm_apply, coindTraceTerm_apply]
      change A.ρ x (f.1 (x⁻¹ * u)) = A.ρ u (A.ρ x (f.1 x⁻¹))
      have hv : x⁻¹ * (u : G) * x ∈ (U : Subgroup G) := by
        simpa using ‹(U : Subgroup G).Normal›.conj_mem _ u.2 x⁻¹
      have e : x⁻¹ * (u : G) = (U : Subgroup G).subtype ⟨_, hv⟩ * x⁻¹ := by
        simp only [Subgroup.subtype_apply]
        group
      rw [e, f.2 ⟨_, hv⟩ x⁻¹]
      change A.ρ x (A.ρ (x⁻¹ * u * x) (f.1 x⁻¹)) = A.ρ u (A.ρ x (f.1 x⁻¹))
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group⟩

omit [IsDiscreteRep A] in

theorem resFunctor_map_coindTrace :
    (Rep.resFunctor (U : Subgroup G).subtype).map (coindTrace (U : Subgroup G) A) =
      ∑ c : G ⧸ (U : Subgroup G), coindTraceTermMor U A c := by
  ext f
  change (coindTrace (U : Subgroup G) A).hom f = (∑ c, coindTraceTermMor U A c).hom f
  rw [coindTrace_hom_apply, Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
  rfl

instance isDiscreteRep_res_coind_res :
    IsDiscreteRep (Rep.res (U : Subgroup G).subtype
      (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_resFunctor_obj_coind_res :
    IsDiscreteRep ((Rep.resFunctor (U : Subgroup G).subtype).obj
      (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))) :=
  isDiscreteRep_res_subtype _ _

theorem cohomologyRes_comp_cohomologyMap_coindTraceTermMor (n : ℕ) (x : G) :
    cohomologyRes (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))
        (U : Subgroup G) n ≫ cohomologyMap (coindTraceTermMor U A (x : G ⧸ (U : Subgroup G))) n =
      shapiroMap U (Rep.res (U : Subgroup G).subtype A) n ≫ cohomologyConj A (U : Subgroup G) n x := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap]
  conv_lhs => rw [← Category.id_comp (cohomologyRes _ _ n), ← cohomologyInnerConj_eq_id n
    (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) x]
  rw [cohomologyRes, cohomologyInnerConj, shapiroMap, cohomologyConj, ← cohomologyMapAlong_comp,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun f => ?_) n
  change coindTraceTerm (U : Subgroup G) A (x : G ⧸ (U : Subgroup G))
      ((Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)).ρ x f) =
    A.ρ x (f.1 1)
  rw [coindTraceTerm_apply]
  change A.ρ x (f.1 (x⁻¹ * x)) = A.ρ x (f.1 1)
  rw [inv_mul_cancel]

theorem cohomologyMap_sum {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {B C : Rep.{u} k Γ} [IsDiscreteRep B] [IsDiscreteRep C] {ι : Type*} (s : Finset ι)
    (f : ι → (B ⟶ C)) (n : ℕ) :
    cohomologyMap (∑ i ∈ s, f i) n = ∑ i ∈ s, cohomologyMap (f i) n := by
  classical
  induction s using Finset.induction with
  | empty => simp [cohomologyMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohomologyMap_add, ih]

theorem cohomologyCores_comp_cohomologyRes (n : ℕ) :
    cohomologyCores U A n ≫ cohomologyRes A (U : Subgroup G) n =
      ∑ c : G ⧸ (U : Subgroup G), cohomologyConj A (U : Subgroup G) n c.out := by
  rw [cohomologyCores, Category.assoc, cohomologyMap_comp_cohomologyRes, resFunctor_map_coindTrace,
    cohomologyMap_sum, Preadditive.comp_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [(QuotientGroup.out_eq' c).symm]
  rw [cohomologyRes_comp_cohomologyMap_coindTraceTermMor, IsIso.inv_hom_id_assoc]

theorem cohomologyRes_cohomologyCores_apply (n : ℕ)
    (x : cohomology (Rep.res (U : Subgroup G).subtype A) n) :
    (cohomologyRes A (U : Subgroup G) n).hom ((cohomologyCores U A n).hom x) =
      ∑ c : G ⧸ (U : Subgroup G), (cohomologyConj A (U : Subgroup G) n c.out).hom x := by
  have h := congrArg (fun f => f.hom x) (cohomologyCores_comp_cohomologyRes U A n)
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.comp_apply, LinearMap.sum_apply]
    using h

end ResCores

section Descent

variable (hA : Function.Bijective fun a : A => (U : Subgroup G).index • a)
include hA

omit [(U : Subgroup G).Normal] in

theorem cohomologyRes_injective_of_bijective (n : ℕ) :
    Function.Injective (cohomologyRes A (U : Subgroup G) n).hom := by
  intro x y h
  have hc : ∀ z : cohomology A n, (cohomologyCores U A n).hom ((cohomologyRes A (U : Subgroup G) n).hom z) =
      (U : Subgroup G).index • z := fun z => by
    rw [← ModuleCat.comp_apply, cohomologyRes_comp_cohomologyCores]
    rfl
  apply (bijective_nsmul_cohomology A _ hA n).1
  change (U : Subgroup G).index • x = (U : Subgroup G).index • y
  rw [← hc, ← hc, h]

theorem range_cohomologyRes_of_bijective (n : ℕ) :
    LinearMap.range (cohomologyRes A (U : Subgroup G) n).hom =
      cohomologyConjInvariants A (U : Subgroup G) n := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact cohomologyRes_apply_mem_cohomologyConjInvariants A _ n z
  · intro x hx
    have hAU : Function.Bijective fun a : Rep.res (U : Subgroup G).subtype A =>
        (U : Subgroup G).index • a := hA
    have hbij := bijective_nsmul_cohomology (Rep.res (U : Subgroup G).subtype A) _ hAU n
    obtain ⟨x', hx'⟩ := hbij.2 x
    simp only at hx'
    have hinv : ∀ g : G, (cohomologyConj A (U : Subgroup G) n g).hom x' = x' := fun g => by
      apply hbij.1
      simp only
      rw [← map_nsmul, hx']
      exact hx g
    refine ⟨(cohomologyCores U A n).hom x', ?_⟩
    rw [cohomologyRes_cohomologyCores_apply]
    simp only [hinv, Finset.sum_const, Finset.card_univ]
    rw [← hx', Subgroup.index_eq_card, Nat.card_eq_fintype_card]

noncomputable def coprimeDescentEquiv (n : ℕ) :
    cohomology A n ≃ₗ[k] cohomologyConjInvariants A (U : Subgroup G) n :=
  LinearEquiv.ofBijective
    ((cohomologyRes A (U : Subgroup G) n).hom.codRestrict _
      (cohomologyRes_apply_mem_cohomologyConjInvariants A _ n))
    ⟨fun x y h => cohomologyRes_injective_of_bijective U A hA n (congrArg Subtype.val h),
      fun x => by
        obtain ⟨z, hz⟩ := (range_cohomologyRes_of_bijective U A hA n).ge x.2
        exact ⟨z, Subtype.ext hz⟩⟩

end Descent

end GroundTheory.ProfCoh
