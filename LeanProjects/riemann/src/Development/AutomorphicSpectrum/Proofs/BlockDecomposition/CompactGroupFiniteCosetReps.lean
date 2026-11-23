import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CosetReps

theorem exists_fin_coset_reps (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J H A : Subgroup G) (hJ : IsCompact (J : Set G)) (hH : IsOpen (H : Set G))
    (_hHJ : H ≤ J) (_hAJ : A ≤ J) (hcov : ∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ H) :
    ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ A) ∧
      ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H := by
  classical
  obtain ⟨t, ht⟩ := hJ.elim_finite_subcover
    (fun a : A => (fun y : G => (a : G)⁻¹ * y) ⁻¹' (H : Set G))
    (fun a => hH.preimage (continuous_const.mul continuous_id))
    (fun y hy => by
      obtain ⟨a, ha, hay⟩ := hcov y hy
      exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, hay⟩)
  let T : Finset (G ⧸ H) := t.image (fun a : A => ((a : G) : G ⧸ H))
  have rep : ∀ q : T, ∃ a : A, ((a : G) : G ⧸ H) = q := by
    rintro ⟨q, hq⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨a, rfl⟩
  choose f hf using rep
  have key : ∀ y ∈ J, ((y : G) : G ⧸ H) ∈ T := by
    intro y hy
    obtain ⟨a, hat, hay⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact Finset.mem_image.2 ⟨a, hat, QuotientGroup.eq.2 hay⟩
  let e : T ≃ Fin T.card := T.equivFin
  have main : ∀ y ∈ J, ∃! i, ((f (e.symm i) : A) : G)⁻¹ * y ∈ H := by
    intro y hy
    refine ⟨e ⟨_, key y hy⟩, ?_, ?_⟩
    · refine QuotientGroup.eq.1 ?_
      rw [Equiv.symm_apply_apply, hf]
    · intro i hi
      have h1 : (((f (e.symm i) : A) : G) : G ⧸ H) = ((y : G) : G ⧸ H) := QuotientGroup.eq.2 hi
      rw [hf] at h1
      rw [← Equiv.symm_apply_eq]
      exact Subtype.ext h1
  obtain ⟨i₀, -⟩ := main 1 J.one_mem
  exact ⟨T.card, i₀.pos, fun i => ((f (e.symm i) : A) : G), fun i => (f (e.symm i)).2, main⟩

end GlobalTheory.CompanionTheory.CosetReps
