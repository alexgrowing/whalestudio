import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
open NumberField

noncomputable section

namespace GlobalTheory.TraceDual

def traceFormMap (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] Module.Dual ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun Y X => -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i))
    (fun Y₁ Y₂ X => by simp [mul_add, Finset.sum_add_distrib]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])
    (fun Y X₁ X₂ => by simp [add_mul, Finset.sum_add_distrib, mul_add]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])

theorem traceFormMap_apply (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Y X : κ → mixedEmbedding.mixedSpace F) :
    traceFormMap F κ Y X = -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := rfl

theorem traceFormMap_injective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Injective (traceFormMap F κ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  have h0 := LinearMap.congr_fun hY (fun i => GlobalTheory.VacLn.TrNondeg.conjM (Y i))
  rw [traceFormMap_apply, LinearMap.zero_apply] at h0
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (neg_eq_zero.1 h) hpi
    · exact h
  have hnn : ∀ i, 0 ≤ Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) := by
    intro i
    rw [GlobalTheory.VacLn.TrNondeg.trace_conjM_mul]
    exact add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
      (Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have e := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h1
  funext i
  exact GlobalTheory.VacLn.TrNondeg.eq_zero_of_trace_conjM_mul _ (e i (Finset.mem_univ _))

theorem traceFormMap_surjective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Surjective (traceFormMap F κ) := by
  have h := Subspace.dual_finrank_eq (K := ℝ) (V := κ → mixedEmbedding.mixedSpace F)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.symm).1
    (traceFormMap_injective F κ)

theorem exists_trace_rep : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ), ∃ Y : κ → mixedEmbedding.mixedSpace F,
      ∀ X, L X = -(2 * Real.pi) * ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := by
  intro F _ _ κ _ L
  obtain ⟨Y, hY⟩ := traceFormMap_surjective F κ L.toLinearMap
  exact ⟨Y, fun X => by rw [← traceFormMap_apply, hY]; rfl⟩

end GlobalTheory.TraceDual
