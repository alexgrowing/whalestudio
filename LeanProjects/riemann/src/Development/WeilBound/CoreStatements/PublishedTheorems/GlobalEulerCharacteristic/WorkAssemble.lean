import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkEndn
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkSplit
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledB
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioEqOneOfCyclic

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_assemble

open PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem ratio_eq_one_of_coprime_cyclic' (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hK : ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (resTo S K' hK' M) ιr' = 1) :
    gsEulerRatio S M ιr = 1 :=
  W_killed_c.ratio_eq_one_of_cyclic ℓ K S hS hSℓ ιr L hL hN M hℓ htriv
    (fun L' _ hL' hle hcyc => W_killed_b.ratio_coind_cyclic ℓ K S hS hSℓ ιr L hL hN M hℓ htriv hK L' hL' hle hcyc)

theorem ratioOneKilled_two (h : RatioOne 2 (fun K => NumberField.IsTotallyComplex K.1)) :
    RatioOneKilled 2 (fun _ => True) := by
  intro K S hS hS2 _ ιr M _ _ h2
  obtain ⟨L, hKL, hL, hN, -, hc, htriv⟩ := W_split.exists_split 2 K S hS hS2 M
  have htc : NumberField.IsTotallyComplex L.1 := hc.resolve_left (by simp)
  exact ratio_eq_one_of_coprime_cyclic' 2 K S hS hS2 ιr L hL hN M h2 htriv
    (W_endn.ending_narrow h K S hS hS2 ιr L hL hN M h2 htriv htc)

theorem ratioOneKilled_of_lemmaX (ℓ : ℕ) [Fact ℓ.Prime] (hX : GlobalEulerCharCoprime) :
    RatioOneKilled ℓ (fun _ => True) := by
  intro K S hS hSℓ _ ιr M _ _ hℓ
  obtain ⟨L, hKL, hL, hN, hζ, hc, htriv⟩ := W_split.exists_split ℓ K S hS hSℓ M
  exact ratio_eq_one_of_coprime_cyclic' ℓ K S hS hSℓ ιr L hL hN M hℓ htriv
    (W_endx.ending_lemmaX hX ℓ K S hS hSℓ ιr L hL hN M hℓ htriv hζ hc)

end PositivityTheory.Lit1.GEN.W_assemble
