import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent

open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

namespace PI.GreenLabelSurjWork

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem glEquiv_val (e : ι ≃ κ) (g : GL ι K) :
    ((glEquiv K e g : GL κ K) : Matrix κ κ K) = Matrix.reindex e e (g : Matrix ι ι K) := rfl

theorem glEquiv_symm_val (e : ι ≃ κ) (g : GL κ K) :
    (((glEquiv K e).symm g : GL ι K) : Matrix ι ι K) = Matrix.reindex e.symm e.symm (g : Matrix κ κ K) := rfl

theorem transp_ρ (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (g : GL κ K) :
    (transp e τ).ρ g = τ.ρ ((glEquiv K e).symm g) := rfl

theorem transp_simple (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (h : Simple τ) : Simple (transp e τ) := by
  rw [FDRep.simple_iff_char_is_norm_one] at h ⊢
  have hc : ∀ g, (transp e τ).character g = τ.character ((glEquiv K e).symm g) := fun g => rfl
  simp only [hc, map_inv]
  rw [Nat.card_congr (glEquiv K e).toEquiv.symm, ← h]
  exact Fintype.sum_equiv (glEquiv K e).symm.toEquiv _ _ (fun g => rfl)

theorem blockUT_reindex {s : ℕ} (e : ι ≃ κ) (b : κ → Fin s) (M : Matrix ι ι K)
    (h : IsBlockUT K (b ∘ e) M) : IsBlockUT K b (Matrix.reindex e e M) := by
  intro i j hij
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact h _ _ (by simpa using hij)

theorem glEquiv_mem_unip {s : ℕ} (e : ι ≃ κ) (b : κ → Fin s) (u : GL ι K)
    (hu : u ∈ unip K (b ∘ e)) : glEquiv K e u ∈ unip K b := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [glEquiv_val]; exact blockUT_reindex e b _ h1
  · rw [← map_inv, glEquiv_val]; exact blockUT_reindex e b _ h2
  · intro i j hij
    rw [glEquiv_val]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [h3 _ _ (by simpa using hij)]
    simp [e.symm.injective.eq_iff]

theorem transp_cusp (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (h : IsCuspidal K τ) :
    IsCuspidal K (transp e τ) := by
  intro s b hb hs v hv
  refine h s (b ∘ e) (hb.comp e.surjective) hs v (fun u hu => ?_)
  have := hv _ (glEquiv_mem_unip e b u hu)
  rwa [transp_ρ, MulEquiv.symm_apply_apply] at this

end PI.GreenLabelSurjWork
