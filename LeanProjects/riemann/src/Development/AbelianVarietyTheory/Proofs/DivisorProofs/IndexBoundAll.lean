import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

namespace GlobalTheory.IdxAll

theorem eq_or_eq_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e τ : E →+* ℂ) (heτ : e.comp (algebraMap F E) = τ.comp (algebraMap F E)) :
    τ = e ∨ ∀ x, τ x = star (e x) := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) e τ heτ
  have hσσ : ∀ x, σ (σ x) = x := fun x => e.injective (by rw [hσ, hσ, star_star])
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσσ) (AlgHom.ext hσσ)
  have hs : s ≠ 1 := by
    intro h1
    refine IsTotallyComplex.complexEmbedding_not_isReal e ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have : σ x = x := congrArg (fun t : E ≃ₐ[F] E => t x) h1
    have h3 := hσ e x
    rw [this] at h3
    exact h3.symm
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases hg1 : g.symm = 1
  · left
    rw [← hg, hg1]
    rfl
  · right
    intro x
    rw [← hg, (hy _ hg1).trans (hy _ hs).symm]
    exact hσ e x

theorem index_bound_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ k : ℕ,
  (∀ w, k ≤ GlobalTheory.Inertia.posIndex (Complex.I • J.map (emb w).1) ∧ k ≤ GlobalTheory.Inertia.negIndex (Complex.I • J.map (emb w).1)) →
  ∀ τ : E →+* ℂ, k ≤ GlobalTheory.Inertia.posIndex (Complex.I • J.map τ) ∧ k ≤ GlobalTheory.Inertia.negIndex (Complex.I • J.map τ) := by
  intro F E _ _ _ _ _ σ h emb n J hJ k hk τ
  haveI := h.1
  set w := InfinitePlace.mk (τ.comp (algebraMap F E)) with hw
  have hreal : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) := IsTotallyReal.complexEmbedding_isReal _
  have he : (emb w).1.comp (algebraMap F E) = τ.comp (algebraMap F E) := by
    rw [(emb w).2, hw, InfinitePlace.embedding_mk_eq_of_isReal hreal]
  rcases eq_or_eq_comp σ h _ _ he with h1 | h1
  · rw [h1]; exact hk w
  · have hH : (Complex.I • J.map (emb w).1).IsHermitian := by
      ext i j
      have h3 := h.2.2.2 (emb w).1 (J j i)
      rw [hJ, map_neg] at h3
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← h3]
      simp
    have h4 : Complex.I • J.map τ = -((Complex.I • J.map (emb w).1).map (starRingEnd ℂ)) := by
      ext i j
      simp [h1]
    rw [h4, GlobalTheory.Inertia.posIndex_neg, GlobalTheory.Inertia.negIndex_neg, GlobalTheory.Inertia.posIndex_map_conj hH,
      GlobalTheory.Inertia.negIndex_map_conj hH]
    exact (hk w).symm

end GlobalTheory.IdxAll
