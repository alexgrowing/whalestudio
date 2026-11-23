import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivisorIdealBotUniformiser
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem idealCycle_support_finite {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    [IsNoetherianRing (MRing ι R)] (J : Ideal (MRing ι R)) :
    (Function.support (idealCycle J)).Finite := by
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J)
  intro W hW
  by_contra hmin
  apply hW
  unfold idealCycle
  rw [dif_neg]
  exact fun h => hmin h.1

theorem finsum_mul_finsum_comm {α β : Type*} (a : α → ℤ) (c : α → β → ℤ) (n : β → ℤ)
    (ha : (Function.support a).Finite) (hc : ∀ W, (Function.support (c W)).Finite) :
    ∑ᶠ W, a W * ∑ᶠ U, c W U * n U = ∑ᶠ U, (∑ᶠ W, a W * c W U) * n U := by
  classical
  set S := ha.toFinset
  set T := S.biUnion (fun W => (hc W).toFinset)
  have hcT : ∀ W ∈ S, Function.support (c W) ⊆ ↑T := by
    intro W hW U hU
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨W, hW, (hc W).mem_toFinset.mpr hU⟩
  have hin : ∀ U, ∑ᶠ W, a W * c W U = ∑ W ∈ S, a W * c W U := by
    intro U
    apply finsum_eq_sum_of_support_subset
    intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW
  simp_rw [hin]
  rw [finsum_eq_sum_of_support_subset (s := S), finsum_eq_sum_of_support_subset (s := T)]
  · rw [Finset.sum_congr rfl (g := fun W => a W * ∑ U ∈ T, c W U * n U)]
    · simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    · intro W hW
      congr 1
      apply finsum_eq_sum_of_support_subset
      intro U hU
      exact hcT W hW (left_ne_zero_of_mul hU)
  · intro U hU
    obtain ⟨W, hW, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hU)
    exact hcT W hW (right_ne_zero_of_mul hne)
  · intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW

theorem RightExpansion.proof (hV : VertCutEff.Statement.{u})
    (hD : DivisorIdealCycle.Statement.{u}) : RightExpansion.Statement.{u} := by
  classical
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hmodel b f g heff c s hs hsP hhor hnc L
  have hPmh : IsMultiHomogIdeal (P ⊔ Ideal.span {s}) :=
    SupSpanMultiHomog.proof O K ι P s c hmodel.multiProj.multiHomog hs
  have key : ∀ W : Ideal (MRing ι O),
      divCycle P s W * (if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) =
        divCycle P s W * cycEval (fun U => vNum U L) (idealCycle (W ⊔ divisorIdeal P f g)) := by
    intro W
    by_cases hW : divCycle P s W = 0
    · rw [hW, zero_mul, zero_mul]
    congr 1
    obtain ⟨hWp, hPW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
    have hWmin : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
      unfold divCycle at hW
      split_ifs at hW with h
      · exact h.1
      · exact absurd rfl hW
    split_ifs with hϖW
    · exact hV O ϖ hϖ K ι P d hmodel b f g heff W s hsP hWmin hWrel
        (MinimalPrimeMultiHomog.proof O K ι _ W hPmh hWmin) hϖW (hnc W hϖW hW) L
    · have hv := hhor W hW hϖW
      have hP : P.IsPrime := hmodel.multiProj.isPrime
      rw [hD O K ι P W f g g f hP hWp hPW heff.1.den_not_mem
        (fun U hU hWU hUrel => heff.2 U hU (hPW.trans hWU) hUrel)
        hv.den_not_mem hv.num_not_mem (by rw [mul_comm, sub_self]; exact P.zero_mem)]
  exact (finsum_congr key).trans <| finsum_mul_finsum_comm _ (fun W U => idealCycle (W ⊔ divisorIdeal P f g) U) _
    (DivCycleFiniteSupport.proof O K ι P s) (fun W => idealCycle_support_finite _)

end GroundTheory.Heights₂.Heights.NumbersDVR
