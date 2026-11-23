import Mathlib
import Formalism.HermitianLattices.StatementLat

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem dualBasic_mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

end SlopeTestRemainingChoices

theorem dualBasic : DualBasic := by
  intro R K V _ _ _ _ _ _ _ _ h hs hst
  have anti : ∀ L M : Submodule R V, L ≤ M → dual h M ≤ dual h L := by
    intro L M hLM x hx
    rw [dualBasic_mem_dual] at hx ⊢
    exact fun y hy => hx y (hLM hy)
  have starOne : ∀ z : K, z ∈ (1 : Submodule R K) → star z ∈ (1 : Submodule R K) := by
    intro z hz
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hz
    obtain ⟨t, ht⟩ := hst r
    exact Submodule.mem_one.2 ⟨t, ht⟩
  have integ : ∀ L : Submodule R V, IsIntegralLat h L ↔ L ≤ dual h L := by
    intro L
    constructor
    · intro hL x hx
      rw [dualBasic_mem_dual]
      exact fun y hy => hL y hy x hx
    · intro hL x hx y hy
      exact (dualBasic_mem_dual h L y).1 (hL hy) x hx
  refine ⟨anti, ?_, ?_, integ, ?_⟩
  · intro L x hx
    rw [dualBasic_mem_dual]
    intro y hy
    have h1 : h x y ∈ (1 : Submodule R K) := (dualBasic_mem_dual h L y).1 hy x hx
    have h2 := starOne _ h1
    have h3 := hs.eq x y
    simp only [starRingEnd_apply] at h3
    rwa [h3] at h2
  · intro L M
    apply le_antisymm
    · exact le_inf (anti _ _ le_sup_left) (anti _ _ le_sup_right)
    · intro x hx
      obtain ⟨hxL, hxM⟩ := Submodule.mem_inf.1 hx
      rw [dualBasic_mem_dual] at hxL hxM ⊢
      intro y hy
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, LinearMap.add_apply]
      exact add_mem (hxL l hl) (hxM m hm)
  · intro L
    rw [IsUnimodular, integ, le_antisymm_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

end Formalism.HermitianLatticesTheory
