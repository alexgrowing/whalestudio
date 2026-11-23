import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem LeftSideAdditiveInDegree.proof : LeftSideAdditiveInDegree.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c₁ c₂ L
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    intro h e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P h e hPmh he) hW'.1,
        hW'.1.1.1, le_sup_left.trans hW'.1.1.2⟩
    · exact absurd rfl hW

  have hadd : ∀ W, ratDiv P f g W ≠ 0 →
      vNum W (Matrix.vecCons (fun k => ((c₁ + c₂) k : ℤ)) L) =
        vNum W (Matrix.vecCons (fun k => (c₁ k : ℤ)) L) +
          vNum W (Matrix.vecCons (fun k => (c₂ k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    obtain ⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · exact hmh g bg hbg W fun hWg => hW (by simp [ratDiv, hWf, hWg])
      · exact hmh f bf hbf W hWf
    have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
    have hdrop := DimStrictDrop.full (MRing ι O) P W hlt
    rw [hP.dim] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [SpecialQuotDim.full O ϖ hϖ K ι W hϖW]
      have e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [e] at hdrop
      exact lt_natCast_of_add_one_le hdrop
    have key := IntNumAddFirst.full (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWm)
      hdim (fun k => (c₁ k : ℤ)) (fun k => (c₂ k : ℤ)) L
    have hsum : (fun k => ((c₁ + c₂) k : ℤ)) = (fun k => (c₁ k : ℤ)) + (fun k => (c₂ k : ℤ)) := by
      funext k; simp
    unfold vNum
    rw [hsum, key]
  have hZfin := ratDiv_support_finite DivCycleFiniteSupport.full P f g
  unfold cutIdentityLeftSide cycEval
  rw [← finsum_add_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
    (hZfin.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  · beta_reduce
    rw [hadd W hW, mul_add]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
