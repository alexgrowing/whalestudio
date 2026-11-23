import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option autoImplicit false

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer

theorem Close.comap_linear : ∀ {I I' : Type} [Fintype I] [Fintype I'] {g g' : ℕ} {W : Opens (Tot I g)} {W' : Opens (Tot I' g')} {C : Type} [CommRing C] (J : Ideal C) (ρ₁ ρ₂ : Hol W' →+* C) (ψ : Hol W →+* Hol W') (M : Fin g → Fin g' → ℂ), (∀ a f, dw a (ψ f) = ∑ b, M b a • ψ (dw b f)) → Close J ρ₁ ρ₂ → Close J (ρ₁.comp ψ) (ρ₂.comp ψ) := by
  intro I I' _ _ g g' W W' C _ J ρ₁ ρ₂ ψ M hψ h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail σ τ _ s ih =>
    obtain ⟨n, h1, h2, h3⟩ := s
    refine Relation.ReflTransGen.tail ih
      ⟨fun b ↦ ∑ a, σ (algebraMap ℂ (Hol W') (M b a)) * n a,
        fun b ↦ J.sum_mem fun a _ ↦ J.mul_mem_left _ (h1 a), fun b c ↦ ?_, fun f ↦ ?_⟩
    · rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun a' _ ↦ ?_
      calc σ (algebraMap ℂ (Hol W') (M b a)) * n a * (σ (algebraMap ℂ (Hol W') (M c a')) * n a')
          = σ (algebraMap ℂ (Hol W') (M b a)) * σ (algebraMap ℂ (Hol W') (M c a')) * (n a * n a') := by ring
        _ = 0 := by rw [h2, mul_zero]
    · simp only [RingHom.comp_apply]
      rw [h3 (ψ f)]
      congr 1
      simp_rw [hψ, map_sum, Algebra.smul_def, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
      ring

end GlobalTheory.AnPer
