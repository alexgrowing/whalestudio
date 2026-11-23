import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ConjRep

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}

theorem map_fixed (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (U : Subgroup G) :
    (fixed ρ U).map (e : V →ₛₗ[starRingEnd ℂ] W) = fixed ρ' U := by
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  constructor
  · rintro ⟨x, hx, hxe⟩
    have hxe' : e x = e v := hxe
    rw [← hxe', GlobalTheory.LGrp.mem_fixed]
    intro k hk
    rw [← he, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
  · intro h
    refine ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => e.injective ?_, rfl⟩
    rw [he, GlobalTheory.LGrp.mem_fixed.1 h k hk]

def comapSub (φ : V →ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, φ (ρ g x) = ρ' g (φ x)) (S : Subrepresentation ρ') :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule.comap φ
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_comap] at hv ⊢
    rw [he]
    exact S.apply_mem_toSubmodule g hv

theorem symm_equivariant (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (g : G) (y : W) :
    e.symm (ρ' g y) = ρ g (e.symm y) := by
  apply e.injective
  rw [he]
  simp

def subOrderIso (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x)) :
    Subrepresentation ρ' ≃o Subrepresentation ρ where
  toFun := comapSub (e : V →ₛₗ[starRingEnd ℂ] W) he
  invFun := comapSub (e.symm : W →ₛₗ[starRingEnd ℂ] V) (symm_equivariant e he)
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    simp [comapSub]
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    simp [comapSub]
  map_rel_iff' := by
    intro S T
    constructor
    · intro h w hw
      obtain ⟨v, rfl⟩ := e.surjective w
      exact @h v hw
    · intro h v hv
      exact @h (e v) hv

theorem isUnitarisable (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x))
    (h : GlobalTheory.LGrp.IsUnitarisable ρ) : GlobalTheory.LGrp.IsUnitarisable ρ' := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => B (e.symm y) (e.symm x)) ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro a b c; simp
  · intro a b c; simp [LinearEquiv.map_smulₛₗ]
  · intro a b c; simp
  · intro a b c; simp [LinearEquiv.map_smulₛₗ]
  · intro v w
    exact h1 _ _
  · intro v hv
    exact h2 _ (by simpa using hv)
  · intro g v w
    simp only [LinearMap.mk₂'ₛₗ_apply, symm_equivariant e he, h3]

theorem conj_transfer : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (φ : V →ₛₗ[starRingEnd ℂ] W), Function.Bijective φ → (∀ g x, φ (ρ g x) = ρ' g (φ x)) → (ρ.IsIrreducible → ρ'.IsIrreducible) ∧ (IsAdmissible ρ → IsAdmissible ρ') ∧ (GlobalTheory.LGrp.IsUnitarisable ρ → GlobalTheory.LGrp.IsUnitarisable ρ') ∧ (GlobalTheory.LGrp.IsSpherical ρ K → GlobalTheory.LGrp.IsSpherical ρ' K) := by
  intro G _ _ K V _ _ W _ _ ρ ρ' φ hφ hρ
  let e : V ≃ₛₗ[starRingEnd ℂ] W := LinearEquiv.ofBijective φ hφ
  have he : ∀ g x, e (ρ g x) = ρ' g (e x) := hρ
  refine ⟨fun h => ?_, fun h => ⟨fun w => ?_, fun U hU hc => ?_⟩, isUnitarisable e he, fun h h0 => h ?_⟩
  · haveI : IsSimpleOrder (Subrepresentation ρ) := h
    exact (subOrderIso e he).isSimpleOrder
  · obtain ⟨v, rfl⟩ := e.surjective w
    have := h.1 v
    convert this using 3 with g
    rw [← he]
    exact e.injective.eq_iff
  · haveI := h.2 U hU hc
    rw [← map_fixed e he U]
    have hfg : (fixed ρ U).FG := Module.Finite.iff_fg.1 inferInstance
    exact Module.Finite.iff_fg.2 (hfg.map _)
  · rw [← map_fixed e he K] at h0
    rw [eq_bot_iff]
    intro v hv
    have : e v ∈ (⊥ : Submodule ℂ W) := h0 ▸ Submodule.mem_map_of_mem hv
    simpa using this

end GlobalTheory.ConjRep
