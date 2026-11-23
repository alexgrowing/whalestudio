import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

section General

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] {T : ShortComplex (Rep.{u} k H)} [IsDiscreteRep T.X₁]
  [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] (φ : H →* G) (hφ : Continuous φ)
  (α : S.map (Rep.resFunctor φ) ⟶ T)

noncomputable def cochainsShortComplexMapAlong :
    cochainsShortComplex S ⟶ cochainsShortComplex T where
  τ₁ := cochainsMapAlong (A := S.X₁) φ hφ α.τ₁
  τ₂ := cochainsMapAlong (A := S.X₂) φ hφ α.τ₂
  τ₃ := cochainsMapAlong (A := S.X₃) φ hφ α.τ₃
  comm₁₂ := by
    ext n x : 3
    apply Subtype.ext
    funext h
    exact congrArg (fun ψ => ψ.hom (((cochainsComplexι S.X₁).f n).hom x (⇑φ ∘ h))) α.comm₁₂
  comm₂₃ := by
    ext n x : 3
    apply Subtype.ext
    funext h
    exact congrArg (fun ψ => ψ.hom (((cochainsComplexι S.X₂).f n).hom x (⇑φ ∘ h))) α.comm₂₃

@[reassoc]
theorem δ_comp_cohomologyMapAlong (hS : S.ShortExact) (hT : T.ShortExact) (i j : ℕ)
    (hij : i + 1 = j) :
    δ hS i j hij ≫ cohomologyMapAlong (A := S.X₁) φ hφ α.τ₁ j =
      cohomologyMapAlong (A := S.X₃) φ hφ α.τ₃ i ≫ δ hT i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsShortComplexMapAlong φ hφ α)
    (cochainsShortComplex_shortExact hS) (cochainsShortComplex_shortExact hT) i j hij

end General

section Restriction

variable (X : ShortComplex (Rep.{u} k G)) [IsDiscreteRep X.X₁] [IsDiscreteRep X.X₂]
  [IsDiscreteRep X.X₃] (U : Subgroup G)

instance isDiscreteRep_map_res_X₁ : IsDiscreteRep (X.map (Rep.resFunctor U.subtype)).X₁ :=
  isDiscreteRep_res_subtype X.X₁ U

instance isDiscreteRep_map_res_X₂ : IsDiscreteRep (X.map (Rep.resFunctor U.subtype)).X₂ :=
  isDiscreteRep_res_subtype X.X₂ U

instance isDiscreteRep_map_res_X₃ : IsDiscreteRep (X.map (Rep.resFunctor U.subtype)).X₃ :=
  isDiscreteRep_res_subtype X.X₃ U

variable {X}

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep X.X₁] [IsDiscreteRep X.X₂]
  [IsDiscreteRep X.X₃] in

theorem shortExact_map_res (hX : X.ShortExact) : (X.map (Rep.resFunctor U.subtype)).ShortExact :=
  (Rep.shortExact_res U.subtype).2 hX

@[reassoc]
theorem δ_comp_cohomologyRes (hX : X.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ cohomologyRes X.X₁ U j =
      cohomologyRes X.X₃ U i ≫ δ (shortExact_map_res U hX) i j hij :=
  δ_comp_cohomologyMapAlong U.subtype (continuous_subgroup_subtype U) (𝟙 _) hX
    (shortExact_map_res U hX) i j hij

end Restriction

section Inflation

variable (X : ShortComplex (Rep.{u} k G)) [IsDiscreteRep X.X₁] [IsDiscreteRep X.X₂]
  [IsDiscreteRep X.X₃] (N : Subgroup G) [N.Normal]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

instance quotientToInvariantsFunctor_preservesZeroMorphisms :
    (Rep.quotientToInvariantsFunctor.{u} k N).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext
    rfl

instance isDiscreteRep_map_quotientToInvariants_X₁ :
    IsDiscreteRep (X.map (Rep.quotientToInvariantsFunctor k N)).X₁ :=
  isDiscreteRep_quotientToInvariants_of_normal X.X₁ N

instance isDiscreteRep_map_quotientToInvariants_X₂ :
    IsDiscreteRep (X.map (Rep.quotientToInvariantsFunctor k N)).X₂ :=
  isDiscreteRep_quotientToInvariants_of_normal X.X₂ N

instance isDiscreteRep_map_quotientToInvariants_X₃ :
    IsDiscreteRep (X.map (Rep.quotientToInvariantsFunctor k N)).X₃ :=
  isDiscreteRep_quotientToInvariants_of_normal X.X₃ N

noncomputable def mapQuotientToInvariantsResToSelf :
    (X.map (Rep.quotientToInvariantsFunctor k N)).map (Rep.resFunctor (QuotientGroup.mk' N)) ⟶
      X where
  τ₁ := Rep.ofHom (X.X₁.ρ.quotientToInvariants_lift N)
  τ₂ := Rep.ofHom (X.X₂.ρ.quotientToInvariants_lift N)
  τ₃ := Rep.ofHom (X.X₃.ρ.quotientToInvariants_lift N)
  comm₁₂ := rfl
  comm₂₃ := rfl

variable {X}

@[reassoc]
theorem δ_comp_cohomologyInfl (hX : X.ShortExact)
    (hXN : (X.map (Rep.quotientToInvariantsFunctor k N)).ShortExact) (i j : ℕ)
    (hij : i + 1 = j) :
    δ hXN i j hij ≫ cohomologyInfl X.X₁ N j = cohomologyInfl X.X₃ N i ≫ δ hX i j hij :=
  δ_comp_cohomologyMapAlong (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N)
    (mapQuotientToInvariantsResToSelf X N) hXN hX i j hij

end Inflation

end GroundTheory.ProfCoh
