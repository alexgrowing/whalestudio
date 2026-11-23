import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LatPull

theorem isVBOn_pull :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E]
      [Module Ω E] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X)
      (i : Ω →+* Ω') (E' : Type) [AddCommGroup E'] [Module Ω' E'] (j : E →+ E') (L : Lat ξ E) (T : Set (Cpt ξ))
      (r : ℕ) (V : Submodule Ω E), Dominates ξ' ξ f i → (∀ (a : Ω) e, j (a • e) = i a • j e) →
      (∀ (n : ℕ) (b : Fin n → E), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) →
      L.IsVBOn T r V →
      (L.pull ξ' f j).IsVBOn {p' | ∃ h : genPt ξ ⤳ f p'.1, (⟨f p'.1, h⟩ : Cpt ξ) ∈ T} r
        (Submodule.span Ω' (j '' V)) := by
  intro X Ω _ ξ E _ _ X' Ω' _ ξ' f i E' _ _ j L T r V hd hj hli hvb p' hp'
  obtain ⟨h, hT⟩ := hp'
  obtain ⟨U, hU, b, hb, hfr⟩ := hvb _ hT
  have hind' : LinearIndependent Ω' fun k => j (b k) := hli r b (hfr _ hT hU).1
  have hbV : ∀ k, b k ∈ V := fun k => hb ▸ Submodule.subset_span ⟨k, rfl⟩
  have key : ∀ v ∈ Submodule.span Ω (Set.range b),
      j v ∈ Submodule.span Ω' (Set.range fun k => j (b k)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [hj]
      exact Submodule.smul_mem _ _ hx
  refine ⟨f ⁻¹ᵁ U, hU, fun k => j (b k), ?_, ?_⟩
  · apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨b k, hbV k, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      exact key v (by rw [hb]; exact hv)
  · rintro q' ⟨h', hT'⟩ hq'
    refine ⟨hind', ?_⟩
    have hL := (hfr _ hT' hq').2
    obtain ⟨h2, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
    have key' : ∀ e ∈ Submodule.span (regAt ξ ⟨f q'.1, h'⟩) (Set.range b),
        j e ∈ Submodule.span (regAt ξ' q') (Set.range fun k => j (b k)) := by
      intro e he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact add_mem hx hy
      | smul a x _ hx =>
        have e1 : j (a • x) = (⟨i a, hreg a a.2⟩ : regAt ξ' q') • j x := hj a x
        rw [e1]
        exact Submodule.smul_mem _ _ hx
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨h3, e, he, rfl⟩
      exact key' e (by rw [← hL]; exact he)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨h', b k, ?_, rfl⟩
      rw [hL]
      exact Submodule.subset_span ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.Ar.LatPull
