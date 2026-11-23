import Mathlib

namespace Bl.FirstLemmaH

theorem goal1 :
  ∀ {A : Type} (W : Submodule.{0, 0} Complex (A → Complex)),
  FiniteDimensional.{0, 0} Complex (Subtype.{1} fun (x : A → Complex) ↦ Membership.mem.{0, 0} W x) →
    Exists.{1} fun (S : Finset.{0} A) ↦
      ∀ (w : A → Complex),
        Membership.mem.{0, 0} W w → (∀ (a : A), Membership.mem.{0, 0} S a → Eq.{1} (w a) 0) → Eq.{1} w 0 := by
  intro A W hW
  classical
  let f : A → Module.Dual Complex W := fun a =>
    (LinearMap.proj (R := Complex) (φ := fun _ : A => Complex) a).comp W.subtype
  have hfg : (Submodule.span Complex (Set.range f)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hsub, heq⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hmem : ∀ φ ∈ s', ∃ a, f a = φ := fun φ h => hsub h
  choose g hg using hmem
  refine ⟨s'.attach.image (fun φ => g φ.1 φ.2), ?_⟩
  intro w hw h0
  have hker : Submodule.span Complex (s' : Set (Module.Dual Complex W)) ≤
      LinearMap.ker (Module.Dual.eval Complex W ⟨w, hw⟩) := by
    rw [Submodule.span_le]
    intro φ hφ
    have e := hg φ hφ
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
    rw [← e]
    exact h0 _ (Finset.mem_image.2 ⟨⟨φ, hφ⟩, Finset.mem_attach _ _, rfl⟩)
  funext a
  have ha : f a ∈ Submodule.span Complex (s' : Set (Module.Dual Complex W)) :=
    heq ▸ Submodule.subset_span ⟨a, rfl⟩
  have h1 := hker ha
  rw [LinearMap.mem_ker, Module.Dual.eval_apply] at h1
  exact h1

end Bl.FirstLemmaH
