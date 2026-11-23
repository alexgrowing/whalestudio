import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberMulExpandStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberRenameStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FibreComponentDivisorPropertiesStatement

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem classList_length_of_mem_support {K σ : Type} (cls : σ → K → ℤ) {m : ℕ}
    {G : MvPolynomial σ ℝ} (hG : G.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ G.support) :
    (classList cls μ).length = m := by
  have h := hG (mem_support_iff.mp hμ)
  have hw : Finsupp.weight (1 : σ → ℕ) μ = μ.sum fun _ => id := by
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hw] at h
  simpa [classList, Multiset.length_toList, Finsupp.card_toMultiset] using h

theorem sum_X_inr_pow_eq {σ : Type} {r : ℕ} (e : Fin r → σ) (k : ℕ) :
    (∑ a, X (Sum.inr (e a)) ^ k : MvPolynomial (σ ⊕ σ) ℝ) =
      rename (Sum.inr ∘ e) (MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin r) ℤ k)) := by
  simp [psum, map_sum, map_pow, rename_X]

theorem val_psum_mul_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (σ : Type) [Fintype σ] (T : LocPair ι O σ), T.IsVert P ϖ → ∀ (r : ℕ) (e : Fin r → σ), PowerSumsVanish P d (T.x' ∘ e) → ∀ k m : ℕ, 1 ≤ k → k + m = d → ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ, (∀ i, (Gs i).IsHomogeneous m) → T.val P (fun i => (∑ a, X (Sum.inr (e a)) ^ k) * Gs i) = 0 := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP σ _ T hT r e hv k m hk hkm Gs hGs
  have hfib := (GlobalTheory.T.fibre_component_divisor_properties O ϖ hϖ K ι P d hP).2.2
  unfold LocPair.val
  refine Finset.sum_eq_zero fun i _ => ?_
  have hZc : ∀ W, ratDiv P (T.f i) (T.g i) W ≠ 0 → IsFibreComp P W := hfib _ _ _ (hT i)
  have hfin : (Function.support (ratDiv P (T.f i) (T.g i))).Finite := by
    refine (Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι O)
      (P ⊔ (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O))).subset ?_
    intro W hW
    exact (hZc W hW).1
  rw [GlobalTheory.T.cycle_number_mul_expand O K ι (σ ⊕ σ) (ratDiv P (T.f i) (T.g i)) (Sum.elim T.x T.x') _ (Gs i) []]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hlen : ((classList (Sum.elim T.x T.x') μ ++ []).length) + k = d := by
    rw [List.append_nil, classList_length_of_mem_support _ (hGs i) hμ]
    omega
  have hcomp : Sum.elim T.x T.x' ∘ (Sum.inr ∘ e) = T.x' ∘ e := by
    funext a
    simp
  rw [sum_X_inr_pow_eq, (GlobalTheory.T.cycle_number_rename).1 O K ι (Fin r) (σ ⊕ σ) (Sum.inr ∘ e), hcomp,
    (cycNum_int_and_comb O K ι (Fin r) (T.x' ∘ e) (classList (Sum.elim T.x T.x') μ ++ [])).1
      (ratDiv P (T.f i) (T.g i)) hfin (psum (Fin r) ℤ k)]
  have hzero : cycEval (fun W => classNum (T.x' ∘ e) (psum (Fin r) ℤ k)
      (classList (Sum.elim T.x T.x') μ ++ []) W) (ratDiv P (T.f i) (T.g i)) = 0 := by
    unfold cycEval
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    by_cases hW : ratDiv P (T.f i) (T.g i) W = 0
    · simp [hW]
    · beta_reduce
      rw [hv W (hZc W hW) k hk _ hlen, mul_zero]
  rw [hzero]
  simp

end GlobalTheory.CompanionTheory.Ar.Num
