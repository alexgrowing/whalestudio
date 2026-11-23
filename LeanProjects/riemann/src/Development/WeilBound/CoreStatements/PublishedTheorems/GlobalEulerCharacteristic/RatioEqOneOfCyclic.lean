import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledC
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkCoinfB
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkQuotV

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_killed_c

local notation "ℚ̄" => AlgebraicClosure ℚ

section GS

theorem ratio_eq_one_of_cyclic (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hcyc : ∀ (L' : FiniteSubfield) [Fact (K ≤ L')]
      (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr = 1) :
    gsEulerRatio S M ιr = 1 := by
  haveI := hN
  haveI := finite_quot_gs K S L hL
  obtain ⟨inst, ρ, hρ, he⟩ := QuotientActionGlobalEulerCharacteristic.quot_rep ℓ K S ιr L hL M hℓ htriv
  rw [he]
  exact eq_one_of_forall_isCyclic (gsOpenSubgroup S hL) (gs_multKilled ℓ K S hS hSℓ ιr)
    (gs_posKilled ℓ K S hS hSℓ ιr) ρ (fun D hD' => by
      obtain ⟨L', hKL', hL', hW, hle, hcycW⟩ := exists_field_of_cyclic ℓ K S ιr L hL D hD'
      have := hcyc L' hL' hle hcycW
      rw [W_coinf_b.coind_eq_infl_funRep ℓ K S ιr L hL M ρ hρ D L' hL' hW] at this
      exact this)

end GS

end PositivityTheory.Lit1.GEN.W_killed_c
