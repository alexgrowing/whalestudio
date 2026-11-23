import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open ReciprocityTheory.AnForm.R.FinalTheorems

namespace GlobalTheory
open IsLocalRing

theorem rsp_append_of_flat_of_isRegularLocalRing_closedFibre :
    ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
      [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ], φ.Flat →
      IsRegularLocalRing (B ⧸ (IsLocalRing.maximalIdeal A).map φ) →
      ∀ (n : ℕ) (r : Fin n → A), Rsp A n r →
        ∃ (g : ℕ) (s : Fin g → B), Rsp B (n + g) (Fin.append (fun i => φ (r i)) s) := by
  intro A B _ _ _ _ _ _ φ _ hflat hreg n r hr
  letI := φ.toAlgebra
  haveI : Module.Flat A B := hflat
  haveI : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  haveI : IsLocalHom (algebraMap A B) := ‹IsLocalHom φ›
  set I : Ideal B := (maximalIdeal A).map φ with hI
  have hIle : I ≤ maximalIdeal B := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit φ x hx
  have hmF : (maximalIdeal B).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (maximalIdeal.isMaximal B) with h | h
    · exfalso
      have h1 : (1 : B ⧸ I) ∈ (maximalIdeal B).map (Ideal.Quotient.mk I) := h ▸ Submodule.mem_top
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
      obtain ⟨y, hy, hy1⟩ := h1
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hy1
      have := (maximalIdeal B).sub_mem hy (hIle hy1)
      simp at this
    · exact IsLocalRing.eq_maximalIdeal h
  have hfg : (maximalIdeal (B ⧸ I)).FG := IsNoetherian.noetherian _
  obtain ⟨t, htcard, htspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  set g := t.card with hg
  let u : Fin g → B ⧸ I := fun i => (t.equivFin.symm i : B ⧸ I)
  have hu : Set.range u = (t : Set (B ⧸ I)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact (t.equivFin.symm i).2
    · intro hx; exact ⟨t.equivFin ⟨x, hx⟩, by simp [u]⟩
  let s : Fin g → B := fun i => Function.surjInv Ideal.Quotient.mk_surjective (u i)
  have hs : ∀ i, Ideal.Quotient.mk I (s i) = u i := fun i => Function.surjInv_eq _ _
  have hcomap : (maximalIdeal (B ⧸ I)).comap (Ideal.Quotient.mk I) = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmapS : (Ideal.span (Set.range s)).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) := by
    rw [Ideal.map_span, ← Set.range_comp, ← htspan, ← hu]
    congr 2
    funext i
    exact hs i
  refine ⟨g, s, ?_, ?_⟩
  · have hspan_r : Ideal.span (Set.range (fun i => φ (r i))) = I := by
      rw [hI, ← hr.1, Ideal.map_span, ← Set.range_comp]
      rfl
    have hrange : Set.range (Fin.append (fun i => φ (r i)) s) =
        Set.range (fun i => φ (r i)) ∪ Set.range s := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · left; exact ⟨j, by simp⟩
        · right; exact ⟨j, by simp⟩
      · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
        · exact ⟨Fin.castAdd g j, by simp⟩
        · exact ⟨Fin.natAdd n j, by simp⟩
    rw [hrange, Ideal.span_union, hspan_r]
    apply le_antisymm
    · refine sup_le hIle ?_
      rw [← hcomap, ← Ideal.map_le_iff_le_comap, hmapS]
    · intro x hx
      rw [← hcomap, Ideal.mem_comap, ← hmapS,
        Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [Ideal.Quotient.eq] at hyx
      have : x = (x - y) + y := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (by simpa using I.neg_mem hyx))
        (Ideal.mem_sup_right hy)
  · have hA : ((maximalIdeal A).height : WithBot ℕ∞) = n := by
      rw [maximalIdeal_height_eq_ringKrullDim, hr.2]
    have hF : ((maximalIdeal (B ⧸ I)).height : WithBot ℕ∞) = g := by
      rw [maximalIdeal_height_eq_ringKrullDim, ← hreg.spanFinrank_maximalIdeal, ← htcard]
    have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A)
      (maximalIdeal B)
    have hIalg : (maximalIdeal A).map (algebraMap A B) = I := rfl
    rw [hIalg, hmF] at H
    rw [← maximalIdeal_height_eq_ringKrullDim, H, WithBot.coe_add, hA, hF]
    push_cast
    rfl

end GlobalTheory
