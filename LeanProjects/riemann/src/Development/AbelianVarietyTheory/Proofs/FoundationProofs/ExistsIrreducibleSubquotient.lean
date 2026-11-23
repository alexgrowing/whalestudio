import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

namespace GlobalTheory.SmoothStabilizerQuotient

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def stab (π : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_maximal (π : Representation ℂ G V) {v : V} (hv : v ≠ 0) :
    ∃ T : Subrepresentation π, Maximal (fun U : Subrepresentation π => v ∉ U.toSubmodule) T := by
  have := zorn_le_nonempty₀ {U : Subrepresentation π | v ∉ U.toSubmodule} ?_ ⊥
    (by
      intro h
      exact hv h)
  · obtain ⟨T, -, hT⟩ := this
    exact ⟨T, hT⟩
  intro c hc hch y hy
  haveI : Nonempty c := ⟨⟨y, hy⟩⟩
  have hdir : Directed (· ≤ ·) (fun U : c => U.1.toSubmodule) := by
    intro a b
    rcases hch.total a.2 b.2 with h | h
    · exact ⟨b, h, le_rfl⟩
    · exact ⟨a, le_rfl, h⟩
  refine ⟨⟨⨆ U : c, U.1.toSubmodule, ?_⟩, ?_, ?_⟩
  · intro g x hx
    rw [Submodule.mem_iSup_of_directed _ hdir] at hx ⊢
    obtain ⟨U, hU⟩ := hx
    exact ⟨U, U.1.apply_mem_toSubmodule g hU⟩
  · intro hx
    obtain ⟨U, hU⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hx
    exact hc U.2 hU
  · intro U hU x hx
    exact (Submodule.mem_iSup_of_directed _ hdir).2 ⟨⟨U, hU⟩, hx⟩

def hull {π : Representation ℂ G V} (T : Subrepresentation π) (v : V) : Subrepresentation π where
  toSubmodule :=
    { carrier := {x | ∀ U : Subrepresentation π, T ≤ U → v ∈ U.toSubmodule → x ∈ U.toSubmodule}
      add_mem' := fun ha hb U h1 h2 => add_mem (ha U h1 h2) (hb U h1 h2)
      zero_mem' := fun U _ _ => zero_mem _
      smul_mem' := fun c _ hx U h1 h2 => U.toSubmodule.smul_mem c (hx U h1 h2) }
  apply_mem_toSubmodule := fun g _ hx U h1 h2 => U.apply_mem_toSubmodule g (hx U h1 h2)

def lift {π : Representation ℂ G V} {σ : Representation ℂ G W} (S : Subrepresentation π)
    (f : S.toRepresentation.IntertwiningMap σ) (R : Subrepresentation σ) : Subrepresentation π where
  toSubmodule := (R.toSubmodule.comap f.toLinearMap).map S.toSubmodule.subtype
  apply_mem_toSubmodule := by
    rintro g _ ⟨x, hx, rfl⟩
    refine ⟨S.toRepresentation g x, ?_, rfl⟩
    have hx' : f x ∈ R.toSubmodule := hx
    show f (S.toRepresentation g x) ∈ R.toSubmodule
    rw [f.isIntertwining]
    exact R.apply_mem_toSubmodule g hx'

theorem mem_lift {π : Representation ℂ G V} {σ : Representation ℂ G W} (S : Subrepresentation π)
    (f : S.toRepresentation.IntertwiningMap σ) (R : Subrepresentation σ) (x : S.toSubmodule) :
    x.1 ∈ (lift S f R).toSubmodule ↔ f x ∈ R.toSubmodule := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain rfl : y = x := Subtype.ext hxy
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

end GlobalTheory.SmoothStabilizerQuotient
