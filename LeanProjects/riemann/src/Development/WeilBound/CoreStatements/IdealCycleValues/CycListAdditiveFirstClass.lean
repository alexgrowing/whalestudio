import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.IdealCycleValues.IntNumLCons
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtOfAddOneLe
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberZeroOfHorizontalStatement

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycList_additive_first_class : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a f hf hfP b b' l hl
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold cycList
  refine AdditivityInDivisor.cycEval_add_fn (DivCycleFiniteSupport.full O K ι P f) fun W hW => ?_
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · have hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes := by
      unfold divCycle at hW
      split_ifs at hW with h
      · exact h.1
      · exact absurd rfl hW
    have hWp : W.IsPrime := hWmin.1.1
    have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.full O K ι _ W
      (SupSpanMultiHomog.full O K ι P f a hP.multiProj.multiHomog hf) hWmin
    have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    have hlt : P < W := lt_of_le_of_ne hPW fun h => hfP (h ▸ hfW)
    have hdim := DimStrictDrop.full (MRing ι O) P W hlt
    rw [hP.dim, ← SpecialQuotDim.full O ϖ hϖ K ι W hϖW,
      show d + 1 + Fintype.card K = l.length + 2 + Fintype.card K by omega] at hdim
    have key := IntNumAddFirst.full _ K ι l.length (specialIdeal W)
      (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWh)
      (AdditivityInDivisor.withBot_lt_of_add_one_le hdim) b b' l.get
    rw [← BaseChangeColon.intNumL_cons, ← BaseChangeColon.intNumL_cons, ← BaseChangeColon.intNumL_cons] at key
    exact key
  · have h0 := GlobalTheory.T.vertical_number_zero_of_horizontal O ϖ hϖ K ι P d hP a f hf hfP W hW hϖW
    show vNumL W _ = vNumL W _ + vNumL W _
    rw [h0 _ (by simpa using hl), h0 _ (by simpa using hl), h0 _ (by simpa using hl), add_zero]
