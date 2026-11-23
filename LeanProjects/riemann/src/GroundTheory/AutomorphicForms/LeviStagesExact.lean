import Mathlib
import GroundTheory.AutomorphicForms.LeviStagesJacquet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ}

section Compact

theorem isClosed_leviUnipotent :
    IsClosed ((leviUnipotent F n β γ : Subgroup (levi F n β)) : Set (levi F n β)) := by
  rw [leviUnipotent, Subgroup.coe_subgroupOf]
  exact isClosed_unipotentRadical.preimage continuous_subtype_val

theorem isClosedEmbedding_leviUnipotent :
    IsClosedEmbedding fun u : leviUnipotent F n β γ => ((u : levi F n β) : GL (Fin n) F) :=
  isClosed_levi.isClosedEmbedding_subtypeVal.comp
    isClosed_leviUnipotent.isClosedEmbedding_subtypeVal

instance locallyCompactSpace_leviUnipotent : LocallyCompactSpace (leviUnipotent F n β γ) :=
  isClosedEmbedding_leviUnipotent.locallyCompactSpace

variable (F n β γ) in

def leviUnipotentToUnipotent : leviUnipotent F n β γ →* unipotentRadical F n γ where
  toFun u := ⟨((u : levi F n β) : GL (Fin n) F), Subgroup.mem_subgroupOf.1 u.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem isClosedEmbedding_leviUnipotentToUnipotent :
    IsClosedEmbedding (leviUnipotentToUnipotent F n β γ) := by
  have hN : IsClosedEmbedding
      (Subtype.val : unipotentRadical F n γ → GL (Fin n) F) :=
    isClosed_unipotentRadical.isClosedEmbedding_subtypeVal
  exact (hN.of_comp_iff).1 isClosedEmbedding_leviUnipotent

theorem exists_compactOpen_leviUnipotent (s : Finset (leviUnipotent F n β γ)) :
    ∃ K : Subgroup (leviUnipotent F n β γ), IsCompact (K : Set (leviUnipotent F n β γ)) ∧
      IsOpen (K : Set (leviUnipotent F n β γ)) ∧ ∀ x ∈ s, x ∈ K := by
  classical
  obtain ⟨K₀, hKc, hKo, hK⟩ :=
    exists_compactOpen_unipotentRadical (s.image (leviUnipotentToUnipotent F n β γ))
  have he := isClosedEmbedding_leviUnipotentToUnipotent (F := F) (n := n) (β := β) (γ := γ)
  refine ⟨K₀.comap (leviUnipotentToUnipotent F n β γ), ?_, ?_, fun x hx => ?_⟩
  · rw [Subgroup.coe_comap]
    exact he.isCompact_preimage hKc
  · rw [Subgroup.coe_comap]
    exact hKo.preimage he.continuous
  · exact Subgroup.mem_comap.2 (hK _ (Finset.mem_image_of_mem _ hx))

end Compact

section Functor

variable {U U' U'' : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup U''] [Module ℂ U''] {σ : Representation ℂ (levi F n β) U}
  {σ' : Representation ℂ (levi F n β) U'} {σ'' : Representation ℂ (levi F n β) U''}

variable (γ) in

def restrictLeviUnipotent (f : Representation.IntertwiningMap σ σ') :
    Representation.IntertwiningMap (σ.comp (leviUnipotent F n β γ).subtype)
      (σ'.comp (leviUnipotent F n β γ).subtype) :=
  ⟨f.toLinearMap, fun u => f.isIntertwining' u⟩

def leviJacquetMap (h : Refines β γ) (f : Representation.IntertwiningMap σ σ') :
    Representation.IntertwiningMap (leviJacquetRep h σ) (leviJacquetRep h σ') :=
  ⟨Representation.Coinvariants.map _ _ (restrictLeviUnipotent γ f), fun m =>
    Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, leviJacquetRep_mk, map_smul,
        Representation.Coinvariants.map_mk]
      congr 2
      exact Representation.IntertwiningMap.isIntertwining _ _ f (h.leviIncl F m) v)⟩

theorem leviJacquetMap_mk (h : Refines β γ) (f : Representation.IntertwiningMap σ σ') (v : U) :
    leviJacquetMap h f (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (f v) := rfl

theorem exact_leviJacquetMap (h : Refines β γ) (hσ' : IsSmooth σ') (hσ'' : IsSmooth σ'')
    (f : Representation.IntertwiningMap σ σ') (g : Representation.IntertwiningMap σ' σ'')
    (hfg : Function.Exact f g) :
    Function.Exact (leviJacquetMap h f) (leviJacquetMap h g) :=
  exact_coinvariantsMap exists_compactOpen_leviUnipotent
    (isSmooth_comp_subtype hσ' _) (isSmooth_comp_subtype hσ'' _)
    (restrictLeviUnipotent γ f) (restrictLeviUnipotent γ g) hfg

end Functor

end Parabolic

end GroundTheory.Automorphic
