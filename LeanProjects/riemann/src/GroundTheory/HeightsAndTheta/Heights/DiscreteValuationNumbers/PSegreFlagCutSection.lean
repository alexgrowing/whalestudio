import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutForms
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisBis
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RelevantMinimalOfDivCycleNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem SegreFlagCutSection.proof (hModel : SegreFlagClosureModel.Statement)
    (hForms : SegreFlagCutForms.Statement) (hDiv : SegreFlagCutDivisor.Statement)
    (hD0 : SegreFlagDegreeZero.Statement) : SegreFlagCutSection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk r a ha
  classical
  set I := pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) with hI
  have hIp : I.IsPrime := (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht (k + 1) (Nat.le_add_left 1 k) hk).1.multiProj.isPrime
  have hpt : ∀ (j : ℕ) (p : Σ k, ι k),
      flagClosurePt y w e φ φ' t j ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p) := fun _ _ => rfl
  have hlift : ∀ i, liftPairForm M M' (a i) ∉ I := fun i hm =>
    ha i ((liftPairForm_mem_iff (hpt (k + 1)) _).1 hm)
  obtain ⟨f₃, g₃, hD₃, hv₃, hk₃⟩ := hD0 O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk

  let bad : MRing (bundleIdx (bundleIdx ι M) M') O → Set (Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) :=
    fun z => {Q | Q ∈ (I ⊔ Ideal.span {z}).minimalPrimes ∧ IsRelevant Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q}
  let T := bad f₃ ∪ bad g₃ ∪ ⋃ i, bad (liftPairForm M M' (a i))
  have hbfin : ∀ z, (bad z).Finite := fun z =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (I ⊔ Ideal.span {z})).subset fun Q hQ => hQ.1
  have hTfin : T.Finite := ((hbfin _).union (hbfin _)).union (Set.finite_iUnion fun i => hbfin _)
  have hbad : ∀ z, ∀ Q ∈ bad z, Q.IsPrime ∧ IsRelevant Q ∧ I ≤ Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q :=
    fun z Q hQ => ⟨hQ.1.1.1, hQ.2.1, le_sup_left.trans hQ.1.1.2, hQ.2.2⟩
  obtain ⟨cs, ch, s, h, hs, hh, hdeg, hsI, hhI, hval, havoid⟩ :=
    hForms O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
      hTfin.toFinset (by
        intro Q hQ
        rcases (hTfin.mem_toFinset.1 hQ) with (hQ | hQ) | hQ
        · exact hbad _ Q hQ
        · exact hbad _ Q hQ
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hQ
          exact hbad _ Q hi)
  have hdiv := hDiv O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
    cs ch s h hs hh hdeg hsI hhI hval
  refine ⟨cs, ch, s, h, f₃, g₃, hs, hh, hdeg, hsI, hhI, hval, hdiv, hD₃, hv₃, hk₃, ?_⟩
  intro H hH hϖH
  by_cases hh0 : divCycle I h H = 0
  ·
    have hs0 : divCycle I s H ≠ 0 := hH.resolve_right (not_not.2 hh0)
    have hne : ratDiv I s h H ≠ 0 := by
      unfold ratDiv
      rw [hh0, sub_zero]
      exact hs0
    rw [hdiv H hϖH] at hne
    split_ifs at hne with hc
    · obtain ⟨hk0, rfl⟩ := hc
      obtain ⟨hf, hg, -⟩ := hk₃ hk0
      exact ⟨hf, hg, fun i hm => ha i ((liftPairForm_mem_iff (hpt k) _).1 hm)⟩
    · exact absurd rfl hne
  ·
    obtain ⟨hmin, hrel⟩ := relevant_minimal_of_divCycle_ne_zero hh0
    have hhH : h ∈ H := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    have avoid : ∀ z, z ∉ I → (H ∈ bad z → H ∈ T) → z ∉ H := by
      intro z hz hT hzH
      exact havoid H (hTfin.mem_toFinset.2 (hT ⟨mem_minimalPrimes_sup_span_of_mem hmin hz hzH, hrel, hϖH⟩)) hhH
    exact ⟨avoid f₃ hD₃.num_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_left _ h'),
      avoid g₃ hD₃.den_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_right _ h'),
      fun i => avoid _ (hlift i) fun h' => Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, h'⟩)⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
