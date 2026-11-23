import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorsCommute
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberLinearStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberMulExpandStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberRenameStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem val_psumExpansion_mul : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] [DecidableEq σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O)) (r k : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) = ∑ μ ∈ G.support, G.coeff μ * (((T.comp e).ck P k (classList (Sum.elim T.x T.x') μ) : ℤ) : ℝ) := by
  intro O _ _ _ K _ _ ι _ σ _ _ T P r k e G
  have hcomp : (Sum.elim T.x T.x') ∘ Sum.map e e = Sum.elim (T.x ∘ e) (T.x' ∘ e) := by
    funext s
    cases s <;> rfl
  have hfin : ∀ f g : MRing ι O, (Function.support (ratDiv P f g)).Finite := fun f g =>
    ratDiv_support_finite DivCycleFiniteSupport.full P f g
  have hterm : ∀ (i : σ) (L : List (K → ℤ)),
      cycNum (ratDiv P (T.f i) (T.g i)) (Sum.elim T.x T.x')
        (∑ a ∈ Finset.univ.filter (fun a => e a = i),
          rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) L =
      ∑ a ∈ Finset.univ.filter (fun a => e a = i),
        ((cycEval (fun W => classNum (Sum.elim (T.x ∘ e) (T.x' ∘ e)) (psumExpansion r k a) L W)
          (ratDiv P (T.f (e a)) (T.g (e a))) : ℤ) : ℝ) := by
    intro i L
    rw [(GlobalTheory.T.cycle_number_linear O K ι (σ ⊕ σ) (ratDiv P (T.f i) (T.g i)) (Sum.elim T.x T.x') L).2.2.1]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain rfl : e a = i := (Finset.mem_filter.mp ha).2
    rw [GlobalTheory.T.cycle_number_rename.1 O K ι (Fin r ⊕ Fin r) (σ ⊕ σ) (Sum.map e e) _ (Sum.elim T.x T.x') _ L, hcomp]
    exact (cycNum_int_and_comb O K ι (Fin r ⊕ Fin r) (Sum.elim (T.x ∘ e) (T.x' ∘ e)) L).1 _
      (hfin _ _) _
  have hck : ∀ L : List (K → ℤ), (((T.comp e).ck P k L : ℤ) : ℝ) =
      ∑ i, ∑ a ∈ Finset.univ.filter (fun a => e a = i),
        ((cycEval (fun W => classNum (Sum.elim (T.x ∘ e) (T.x' ∘ e)) (psumExpansion r k a) L W)
          (ratDiv P (T.f (e a)) (T.g (e a))) : ℤ) : ℝ) := by
    intro L
    rw [Finset.sum_fiberwise]
    simp only [LocPair.ck, pairNum, LocPair.comp, Function.comp_apply, Int.cast_sum]
  unfold LocPair.val
  simp only [GlobalTheory.T.cycle_number_mul_expand O K ι (σ ⊕ σ), List.append_nil, hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.mul_sum, hck]

end GlobalTheory.CompanionTheory.Ar.Num
