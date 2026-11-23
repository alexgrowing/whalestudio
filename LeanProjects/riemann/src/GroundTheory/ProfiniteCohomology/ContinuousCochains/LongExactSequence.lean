import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory ShortComplex

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cochainsMap_zero {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] :
    cochainsMap (0 : A ⟶ B) = 0 := by
  ext n c : 3
  rfl

theorem cohomologyMap_zero {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (n : ℕ) :
    cohomologyMap (0 : A ⟶ B) n = 0 := by
  rw [cohomologyMap, cochainsMap_zero]
  exact HomologicalComplex.homologyMap_zero _ _ _

section

variable (S : ShortComplex (Rep.{u} k G)) [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]

noncomputable def cochainsShortComplex : ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  ShortComplex.mk (cochainsMap S.f) (cochainsMap S.g) (by
    rw [← cochainsMap_comp, S.zero, cochainsMap_zero])

variable {S}

theorem cochainsShortComplex_shortExact (hS : S.ShortExact) :
    (cochainsShortComplex S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro x₂ hx₂
      let c : locallyConstantCochains S.X₂ i := x₂
      have hexact := hS.exact.map (forget₂ (Rep.{u} k G) (ModuleCat k))
      rw [ShortComplex.moduleCat_exact_iff] at hexact
      have hval : ∀ σ, S.g.hom (c.1 σ) = 0 := fun σ =>
        congrArg (fun x : locallyConstantCochains S.X₃ i => x.1 σ) hx₂
      let t : S.X₂ → S.X₁ := Function.invFun S.f.hom
      have ht : ∀ σ, S.f.hom (t (c.1 σ)) = c.1 σ := fun σ =>
        Function.invFun_eq (hexact (c.1 σ) (hval σ))
      refine ⟨(⟨t ∘ c.1, (mem_locallyConstantCochains _ _).2 (IsLocallyConstant.comp c.2 t)⟩ :
        locallyConstantCochains S.X₁ i), ?_⟩
      apply Subtype.ext
      funext σ
      exact ht σ
    mono_f := by
      have := hS.mono_f
      exact (inferInstance : Mono ((cochainsMap S.f).f i))
    epi_g := by
      have := hS.epi_g
      exact (inferInstance : Epi ((cochainsMap S.g).f i)) }

variable (hS : S.ShortExact)

noncomputable def δ (i j : ℕ) (hij : i + 1 = j) : cohomology S.X₃ i ⟶ cohomology S.X₁ j :=
  (cochainsShortComplex_shortExact hS).δ i j hij

@[reassoc (attr := simp)]
theorem δ_comp (i j : ℕ) (hij : i + 1 = j) : δ hS i j hij ≫ cohomologyMap S.f j = 0 :=
  (cochainsShortComplex_shortExact hS).δ_comp i j hij

@[reassoc (attr := simp)]
theorem comp_δ (i j : ℕ) (hij : i + 1 = j) : cohomologyMap S.g i ≫ δ hS i j hij = 0 :=
  (cochainsShortComplex_shortExact hS).comp_δ i j hij

theorem cohomologyMap_f_comp_g (i : ℕ) : cohomologyMap S.f i ≫ cohomologyMap S.g i = 0 := by
  rw [← cohomologyMap_comp, S.zero, cohomologyMap_zero]

theorem cohomology_exact₁ (i j : ℕ) (hij : i + 1 = j) :
    (ShortComplex.mk (δ hS i j hij) (cohomologyMap S.f j) (δ_comp hS i j hij)).Exact :=
  (cochainsShortComplex_shortExact hS).homology_exact₁ i j hij

include hS in

theorem cohomology_exact₂ (i : ℕ) :
    (ShortComplex.mk (cohomologyMap S.f i) (cohomologyMap S.g i)
      (cohomologyMap_f_comp_g i)).Exact :=
  (cochainsShortComplex_shortExact hS).homology_exact₂ i

theorem cohomology_exact₃ (i j : ℕ) (hij : i + 1 = j) :
    (ShortComplex.mk (cohomologyMap S.g i) (δ hS i j hij) (comp_δ hS i j hij)).Exact :=
  (cochainsShortComplex_shortExact hS).homology_exact₃ i j hij

end

section Naturality

variable {S₁ S₂ : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S₁.X₁] [IsDiscreteRep S₁.X₂]
  [IsDiscreteRep S₁.X₃] [IsDiscreteRep S₂.X₁] [IsDiscreteRep S₂.X₂] [IsDiscreteRep S₂.X₃]

noncomputable def cochainsShortComplexMap (φ : S₁ ⟶ S₂) :
    cochainsShortComplex S₁ ⟶ cochainsShortComplex S₂ where
  τ₁ := cochainsMap φ.τ₁
  τ₂ := cochainsMap φ.τ₂
  τ₃ := cochainsMap φ.τ₃
  comm₁₂ := by
    change cochainsMap φ.τ₁ ≫ cochainsMap S₂.f = cochainsMap S₁.f ≫ cochainsMap φ.τ₂
    rw [← cochainsMap_comp, ← cochainsMap_comp, φ.comm₁₂]
  comm₂₃ := by
    change cochainsMap φ.τ₂ ≫ cochainsMap S₂.g = cochainsMap S₁.g ≫ cochainsMap φ.τ₃
    rw [← cochainsMap_comp, ← cochainsMap_comp, φ.comm₂₃]

theorem δ_naturality (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (i j : ℕ)
    (hij : i + 1 = j) :
    δ hS₁ i j hij ≫ cohomologyMap φ.τ₁ j = cohomologyMap φ.τ₃ i ≫ δ hS₂ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsShortComplexMap φ)
    (cochainsShortComplex_shortExact hS₁) (cochainsShortComplex_shortExact hS₂) i j hij

end Naturality

end GroundTheory.ProfCoh
