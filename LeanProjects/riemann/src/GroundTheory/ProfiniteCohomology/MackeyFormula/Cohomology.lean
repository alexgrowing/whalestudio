import Mathlib
import GroundTheory.ProfiniteCohomology.MackeyFormula
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.InnerConj
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomApplyHomApplyEqOfCompEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

section Additive

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {A B : Rep.{u} k Γ} [IsDiscreteRep A] [IsDiscreteRep B]

private theorem cochainsMap_add_alt (f g : A ⟶ B) :
    cochainsMap (f + g) = cochainsMap f + cochainsMap g := by
  ext n c : 3
  apply Subtype.ext
  funext x
  rfl

private noncomputable def cohomologyMapAddHom (n : ℕ) :
    (A ⟶ B) →+ (cohomology A n ⟶ cohomology B n) where
  toFun f := cohomologyMap f n
  map_zero' := cohomologyMap_zero n
  map_add' f g := by
    rw [cohomologyMap, cochainsMap_add_alt]
    exact HomologicalComplex.homologyMap_add _ _ _

private theorem cohomologyMap_sum_alt {J : Type*} (s : Finset J) (f : J → (A ⟶ B)) (n : ℕ) :
    cohomologyMap (∑ j ∈ s, f j) n = ∑ j ∈ s, cohomologyMap (f j) n :=
  map_sum (cohomologyMapAddHom n) f s

end Additive

section Conj

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]
  (V : OpenSubgroup G) (ι : H →ₜ* G)

def mackeyConjₜ (x : G) : mackeySubgroup (V : Subgroup G) ι.toMonoidHom x →ₜ* (V : Subgroup G) :=
  ⟨mackeyConj (V : Subgroup G) ι.toMonoidHom x,
    continuous_mackeyConj V (continuous_toMonoidHom ι) x⟩

@[simp]
theorem mackeyConjₜ_toMonoidHom (x : G) :
    (mackeyConjₜ V ι x).toMonoidHom = mackeyConj (V : Subgroup G) ι.toMonoidHom x :=
  rfl

end Conj

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (V : OpenSubgroup G) (ι : H →ₜ* G) (N : Rep.{u} k (V : Subgroup G)) [IsDiscreteRep N]

instance isDiscreteRep_res_coind :
    IsDiscreteRep (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) :=
  IsDiscreteRep.res (continuous_toMonoidHom ι) _

instance isDiscreteRep_mackeyRep_continuousMonoidHom (x : G) :
    IsDiscreteRep (mackeyRep (V : Subgroup G) ι.toMonoidHom N x) :=
  isDiscreteRep_mackeyRep V (continuous_toMonoidHom ι) N x

instance isDiscreteRep_mackeySummand (x : G) :
    IsDiscreteRep (mackeySummand (V : Subgroup G) ι.toMonoidHom N x) :=
  @isDiscreteRep_coind k H _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) x)
    (mackeyRep (V : Subgroup G) ι.toMonoidHom N x)
    (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N x) _

noncomputable instance fintype_mackeyDoubleCoset :
    Fintype (MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) :=
  have := finite_mackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom
  Fintype.ofFinite _

noncomputable def mackeyCohomologyMap (x : G) (n : ℕ) :
    cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n ⟶
      cohomology (mackeyRep (V : Subgroup G) ι.toMonoidHom N x) n :=
  cohomologyMap (mackeyProj (V : Subgroup G) ι.toMonoidHom N x) n ≫
    cohomologyMapAlong (mackeySubgroup (V : Subgroup G) ι.toMonoidHom x).subtype
      (continuous_subgroup_subtype _)
      (coindEvalOne (mackeySubgroup (V : Subgroup G) ι.toMonoidHom x)
        (mackeyRep (V : Subgroup G) ι.toMonoidHom N x)) n

omit [CompactSpace G] in
theorem isIso_shapiroMap_mackey (x : G) (n : ℕ) :
    IsIso (@shapiroMap k H _ _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) x)
      (mackeyRep (V : Subgroup G) ι.toMonoidHom N x)
      (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N x) n) :=
  @isIso_shapiroMap' k H _ _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) x)
      (mackeyRep (V : Subgroup G) ι.toMonoidHom N x)
      (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N x) n

theorem mackeyCohomology_bijective (n : ℕ) :
    Function.Bijective fun (c : cohomology (Rep.res ι.toMonoidHom
        (Rep.coind (V : Subgroup G).subtype N)) n)
        (d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) =>
      (mackeyCohomologyMap V ι N d.out n).hom c := by
  classical
  set P := fun d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom =>
    cohomologyMap (mackeyProj (V : Subgroup G) ι.toMonoidHom N d.out) n
  set I := fun d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom =>
    cohomologyMap (mackeyIncl (V : Subgroup G) ι.toMonoidHom N d) n
  have hIP : ∀ d, I d ≫ P d = 𝟙 _ := fun d => by
    simp only [I, P]
    rw [← cohomologyMap_comp, mackeyIncl_comp_mackeyProj, cohomologyMap_id]
  have hIP' : ∀ d d', d ≠ d' → I d ≫ P d' = 0 := fun d d' h => by
    simp only [I, P]
    rw [← cohomologyMap_comp, mackeyIncl_comp_mackeyProj_of_ne _ _ _ h, cohomologyMap_zero]
  have hsum : ∑ d, P d ≫ I d = 𝟙 _ := by
    simp only [I, P]
    simp_rw [← cohomologyMap_comp]
    rw [← cohomologyMap_sum_alt, sum_mackeyProj_comp_mackeyIncl, cohomologyMap_id]
  set S := fun d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom =>
    @shapiroMap k H _ _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) d.out)
      (mackeyRep (V : Subgroup G) ι.toMonoidHom N d.out)
      (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N d.out) n
  have key : ∀ d c, (mackeyCohomologyMap V ι N d.out n).hom c = (S d).hom ((P d).hom c) :=
    fun _ _ => rfl
  have hS : ∀ d, Function.Bijective (S d).hom := fun d => by
    have := isIso_shapiroMap_mackey V ι N d.out n
    exact ConcreteCategory.bijective_of_isIso _
  constructor
  · intro c c' hcc
    have hP : ∀ d, (P d).hom c = (P d).hom c' := fun d => by
      have h1 := congrFun hcc d
      simp only [key] at h1
      exact (hS d).1 h1
    have e : ∀ c₀, c₀ = ∑ d, (I d).hom ((P d).hom c₀) := fun c₀ => by
      have := congrArg (fun φ => φ.hom c₀) hsum
      rw [ModuleCat.hom_sum, LinearMap.sum_apply] at this
      exact this.symm
    rw [e c, e c']
    simp only [hP]
  · intro y
    choose z hz using fun d => (hS d).2 (y d)
    refine ⟨∑ d, (I d).hom (z d), funext fun d' => ?_⟩
    change (mackeyCohomologyMap V ι N d'.out n).hom (∑ d, (I d).hom (z d)) = y d'
    rw [key, map_sum, Finset.sum_eq_single d']
    · rw [hom_apply_hom_apply_of_comp_eq (hIP d') (z d')]
      exact hz d'
    · intro d _ hd
      rw [hom_apply_hom_apply_of_comp_eq (hIP' d d' hd) (z d)]
      rfl
    · intro h
      exact absurd (Finset.mem_univ d') h

noncomputable def mackeyCohomologyPi (n : ℕ) :
    cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n →ₗ[k]
      ∀ d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom,
        cohomology (mackeyRep (V : Subgroup G) ι.toMonoidHom N d.out) n :=
  LinearMap.pi fun d => (mackeyCohomologyMap V ι N d.out n).hom

theorem mackeyCohomologyPi_apply (n : ℕ)
    (c : cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n)
    (d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) :
    mackeyCohomologyPi V ι N n c d = (mackeyCohomologyMap V ι N d.out n).hom c :=
  rfl

theorem mackeyCohomologyPi_bijective (n : ℕ) : Function.Bijective (mackeyCohomologyPi V ι N n) := by
  have h := mackeyCohomology_bijective V ι N n
  refine ⟨fun c c' hc => h.1 (funext fun d => ?_), fun y => ?_⟩
  · have := congrFun hc d
    rwa [mackeyCohomologyPi_apply, mackeyCohomologyPi_apply] at this
  · obtain ⟨c, hc⟩ := h.2 y
    exact ⟨c, funext fun d => (mackeyCohomologyPi_apply V ι N n c d).trans (congrFun hc d)⟩

noncomputable def mackeyCohomologyEquiv (n : ℕ) :
    cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n ≃ₗ[k]
      ∀ d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom,
        cohomology (mackeyRep (V : Subgroup G) ι.toMonoidHom N d.out) n :=
  LinearEquiv.ofBijective (mackeyCohomologyPi V ι N n) (mackeyCohomologyPi_bijective V ι N n)

theorem mackeyCohomologyEquiv_apply (n : ℕ)
    (c : cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n)
    (d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) :
    mackeyCohomologyEquiv V ι N n c d = (mackeyCohomologyMap V ι N d.out n).hom c :=
  rfl

theorem cohomologyMapAlong_comp_mackeyCohomologyMap (x : G) (n : ℕ) :
    cohomologyMapAlong ι.toMonoidHom (continuous_toMonoidHom ι)
        (𝟙 (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N))) n ≫
      mackeyCohomologyMap V ι N x n =
    shapiroMap V N n ≫ cohomologyMapAlong (mackeyConj (V : Subgroup G) ι.toMonoidHom x)
      (continuous_toMonoidHom (mackeyConjₜ V ι x)) (𝟙 _) n := by
  rw [← Category.id_comp (cohomologyMapAlong ι.toMonoidHom _ _ n),
    ← cohomologyInnerConj_eq_id n (Rep.coind (V : Subgroup G).subtype N) x⁻¹,
    mackeyCohomologyMap, ← cohomologyMapAlong_id_eq_cohomologyMap, shapiroMap_eq,
    cohomologyInnerConj, Category.assoc]
  rw [← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine Eq.trans ?_ (cohomologyMapAlong_comp _ _ _ _ _ _ n)
  refine cohomologyMapAlong_congr _ _ _ _ ?_ (fun f => ?_) n
  · ext h
    change x⁻¹⁻¹ * ι.toMonoidHom (h : H) * x⁻¹ = x * ι.toMonoidHom (h : H) * x⁻¹
    rw [inv_inv]
  · change f.1 (x * ι.toMonoidHom 1 * x⁻¹) = f.1 1
    rw [map_one, mul_one, mul_inv_cancel]

theorem mackeyCohomologyEquiv_cohomologyMapAlong (n : ℕ)
    (c : cohomology (Rep.coind (V : Subgroup G).subtype N) n)
    (d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) :
    mackeyCohomologyEquiv V ι N n ((cohomologyMapAlong ι.toMonoidHom (continuous_toMonoidHom ι)
        (𝟙 (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N))) n).hom c) d =
      (cohomologyMapAlong (mackeyConj (V : Subgroup G) ι.toMonoidHom d.out)
        (continuous_toMonoidHom (mackeyConjₜ V ι d.out)) (𝟙 _) n).hom ((shapiroMap V N n).hom c) := by
  rw [mackeyCohomologyEquiv_apply]
  exact hom_apply_hom_apply_eq_of_comp_eq (cohomologyMapAlong_comp_mackeyCohomologyMap V ι N d.out n) c

end GroundTheory.ProfCoh
