import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkAdmF

theorem placesOver_three_nonempty (D : D7) : (placesOver D.host.E 3).Nonempty := by
  have hl : Nat.Prime 3 := Nat.prime_three
  have hne : ((3 : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hnu : ¬ IsUnit ((3 : ℕ) : 𝓞 D.host.E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ)
    have h2 : Algebra.norm ℤ ((3 : ℕ) : 𝓞 D.host.E) = ((3 : ℕ) : ℤ) ^ Module.finrank ℤ (𝓞 D.host.E) := by
      rw [← Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 D.host.E) ((3 : ℕ) : ℤ)]; simp
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
    exact hl.one_lt.ne' h1
  obtain ⟨M, hM, hlM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hnu)
  exact ⟨⟨M, hM.isPrime, fun h => hne (by simp [h] at hlM)⟩, hlM⟩

theorem sumOver_three_even (D : D7) (c : ℝ) :
    TwistedPlaces.sumOver D 3 (fun _ => c / ((placesOver D.host.E 3).ncard : ℝ)) = c := by
  have hfin : (placesOver D.host.E 3).Finite := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
  have hpos : 0 < (placesOver D.host.E 3).ncard :=
    (Set.ncard_pos hfin).2 (placesOver_three_nonempty D)
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hfin]
  have : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

theorem localBoundTableAllPrimes_conditionTwoThree : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  intro D L P X C tf _ hF i hi hl
  have hFi := hF i hi hl
  by_cases h2 : D.nd.l i ∈ D.host.small
  · have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    show TwistedPlaces.sumOver D _ ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    rw [hlen, hBB]
    have h0 : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by simp [TwistedPlaces.sumOver]
    rw [h0, zero_add]
    exact hFi
  · have h3 : D.nd.l i = 3 := hl.resolve_left h2
    have hq : D.host.q ≠ 3 := D.host.q_ne_three
    have hd : D.host.d ≠ 3 := by
      have := D.host.hyp.2.2.2.1
      omega
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    have hBB : (tab L X tf C).BB i = 0 := by
      have h1 : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by omega
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg h1, if_neg hR]
    show TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    have hFi' : TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i ≤ _ := hFi
    rw [h3] at hFi'
    rw [hlen, hBB, h3, sumOver_three_even, add_zero]
    exact hFi'

end GlobalTheory.NLinkAdmF

end
