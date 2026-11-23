import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvAtParabNeZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.MaschkeForms

open Representation

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_of_isAtom {π : Representation ℂ G V} {U : Subrepresentation π}
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  have hne : U.toSubmodule ≠ ⊥ := fun h => hU.1 (Subrepresentation.toSubmodule_injective h)
  have hnt : Nontrivial (Subrepresentation U.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h' : (⊥ : Submodule ℂ U.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← U.toSubmodule.map_subtype_top, ← h', Submodule.map_bot]
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation π := ⟨S.toSubmodule.map U.toSubmodule.subtype, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, S.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hT : T ≤ U := U.toSubmodule.map_subtype_le S.toSubmodule
  have hinj := Submodule.map_injective_of_injective U.toSubmodule.injective_subtype
  rcases hU.le_iff.mp hT with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans (Submodule.map_bot _).symm
  · right
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans U.toSubmodule.map_subtype_top.symm

def orbitSpan (π : Representation ℂ G V) (x : V) : Subrepresentation π where
  toSubmodule := Submodule.span ℂ (Set.range fun h : G => π h x)
  apply_mem_toSubmodule g v hv := by
    have : Submodule.span ℂ (Set.range fun h : G => π h x) ≤
        (Submodule.span ℂ (Set.range fun h : G => π h x)).comap (π g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by show π (g * h) x = π g (π h x); rw [map_mul]; rfl⟩
    exact this hv

theorem isCompl_toSubmodule {π : Representation ℂ G V} {S T : Subrepresentation π} (h : IsCompl S T) :
    IsCompl S.toSubmodule T.toSubmodule := by
  constructor
  · rw [disjoint_iff]; exact congrArg Subrepresentation.toSubmodule h.inf_eq_bot
  · rw [codisjoint_iff]; exact congrArg Subrepresentation.toSubmodule h.sup_eq_top

theorem proj_left {π : Representation ℂ G V} {S T : Subrepresentation π} (h : IsCompl S T) (v : V)
    (hv : v ∈ S.toSubmodule) :
    S.toSubmodule.projectionOnto T.toSubmodule (isCompl_toSubmodule h) v = ⟨v, hv⟩ :=
  Submodule.projectionOnto_apply_left (isCompl_toSubmodule h) ⟨v, hv⟩

theorem proj_right {π : Representation ℂ G V} {S T : Subrepresentation π} (h : IsCompl S T) (v : V)
    (hv : v ∈ T.toSubmodule) :
    S.toSubmodule.projectionOnto T.toSubmodule (isCompl_toSubmodule h) v = 0 :=
  Submodule.projectionOnto_apply_right (isCompl_toSubmodule h) ⟨v, hv⟩

def proj {π : Representation ℂ G V} {S T : Subrepresentation π} (h : IsCompl S T) :
    π.IntertwiningMap S.toRepresentation :=
  (S.toSubmodule.projectionOnto T.toSubmodule (isCompl_toSubmodule h)).intertwiningMap_of_isIntertwiningMap
    π S.toRepresentation (by
      intro g v
      have hv : v ∈ S.toSubmodule ⊔ T.toSubmodule := by
        rw [(isCompl_toSubmodule h).sup_eq_top]; exact Submodule.mem_top
      obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add, map_add, map_add, proj_left h _ (S.apply_mem_toSubmodule g hs),
        proj_right h _ (T.apply_mem_toSubmodule g ht), proj_left h s hs, proj_right h t ht, add_zero, add_zero]
      rfl)

end GlobalTheory.MaschkeForms
