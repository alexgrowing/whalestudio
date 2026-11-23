import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialOfConjTorus

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc GlobalTheory.CompanionTheory.LbElem.ConjMonomial

namespace GlobalTheory.CompanionTheory.LbElem.MonomialInJ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem diag_ne_zero_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) (i : Fin N) :
    (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
  intro h0
  have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i i) (mul_inv_cancel x)
  simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [Finset.sum_eq_zero] at h1
  · exact zero_ne_one h1
  · intro l _
    by_cases hl : i = l
    · subst hl
      rw [h0, zero_mul]
    · rw [h i l hl, zero_mul]

private def o {N : ℕ} (a : Fin N) : Fin (ones N a) := ⟨0, by simp [ones]⟩

theorem nup_entries {N : ℕ} {c : GL (Fin N) k} (hc : c ∈ unipRad k (stdBlocks (ones N) (sum_ones N))) :
    (∀ i j : Fin N, j < i → (c : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i : Fin N, (c : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hc
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := mem_parab_iff.1 h1 i j (o i) (o j) hij
    rwa [stdBlocks_ones, stdBlocks_ones] at this
  · have := h2 i (o i) (o i)
    rwa [stdBlocks_ones, Matrix.one_apply_eq] at this

theorem nlo_entries {N : ℕ} {a : GL (Fin N) k}
    (ha : a ∈ unipRadLower k (stdBlocks (ones N) (sum_ones N))) :
    (∀ i j : Fin N, i < j → (a : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i : Fin N, (a : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := (mem_unipRadLower k).1 ha
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := (mem_parabLower_iff k).1 h1 i j (o i) (o j) hij
    rwa [stdBlocks_ones, stdBlocks_ones] at this
  · have := h2 i (o i) (o i)
    rwa [stdBlocks_ones, Matrix.one_apply_eq] at this

end GlobalTheory.CompanionTheory.LbElem.MonomialInJ

end
