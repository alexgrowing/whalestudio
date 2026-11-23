import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsZmodPrimeRepresentationOfTorsion
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.DescGS
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsComplexConjugationAtRealPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.GwCount

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem plDvd_fin (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : N ≠ 0) : (plDvd F N).Finite := by
  have h : Ideal.span {((N : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Ws.card_globalCocycles_le_of_iwasawaRank :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (N r g : ℕ), l ≠ 2 → N ≠ 0 → l ∣ N → (plDvd F N).ncard ≤ g → (∀ σ ∈ ineOff F Ω N, ∀ m, ρ σ m = m) → K.Normal → IsOpen (K : Set (G F Ω)) → ¬ l ∣ K.index → (∀ σ ∈ K, ∀ m, ρ σ m = m) → K ≤ (cycMod F Ω l 1).ker → XRk l 1 K r → CardLe (cocOff ρ (ineOff F Ω N)) (Nat.card M ^ (r + 2 + g + Module.finrank ℚ F)) ∧ (IsTotallyReal F → (∀ σ : G F Ω, IsCC σ → ∀ m, ρ σ m = m) → CardLe (cocOff ρ (ineOff F Ω N)) (Nat.card M ^ (r + 2 + g))) := by
  intro P F Ω _ _ _ _ _ l _ R M _ _ _ _ hlM ρ K N r g hl hN hlN hg hI hKn hKo hKi hKρ hKc hX
  obtain ⟨inst, ρ', hρ'⟩ := exists_zmod_prime_representation_of_torsion l (G F Ω) R M hlM ρ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hfin := plDvd_fin F N hN
  have hcard : hfin.toFinset.card ≤ g := by rwa [← Set.ncard_eq_toFinset_card _ hfin]
  have hmem : ∀ v, v ∈ plDvd F N → v ∈ hfin.toFinset := fun v hv => hfin.mem_toFinset.2 hv
  generalize hfin.toFinset = S at hcard hmem
  have hS : ContainsAbove S l := fun v hv => hmem v (by
    obtain ⟨k, rfl⟩ := hlN
    show ((l * k : ℕ) : 𝓞 F) ∈ v.asIdeal
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hv)
  obtain ⟨ρS, h1, h2, h3⟩ := exists_descent_to_galoisGroupUnramifiedOutside F Ω (ZMod (l ^ 1)) M S ρ' K N hmem
    (fun σ h m => by rw [hρ', hI σ h]) hKo (fun σ h m => by rw [hρ', hKρ σ h])
  have hc : ∀ w : InfinitePlace F, ∃ c : G F Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · obtain ⟨c, hc⟩ := exists_complexConjugation_at_realPlace F Ω w hw
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose c hc using hc
  obtain ⟨hZ, hb⟩ := greenberg_wiles_count_mod_l P F Ω l M S ρS K r c hl hS h2 hKn hKi
    (fun σ h m => by rw [h1, hρ', hKρ σ h]) hKc hX hc
  have hM : 0 < Nat.card M := Nat.card_pos
  have hex : ∀ z : cocOff ρ (ineOff F Ω N), ∃ y : Z1 ρS, ∀ g, y.1 (toGS Ω _ g) = z.1 g := fun z => by
    obtain ⟨y, hy, e⟩ := h3 z.1 ⟨z.2.1, fun a b => by rw [hρ']; exact z.2.2.1 a b, z.2.2.2⟩
    exact ⟨⟨y, hy⟩, e⟩
  choose f hf using hex
  have hinj : Function.Injective f := fun a b h => Subtype.ext (funext fun x => by rw [← hf, ← hf, h])
  have hb' : Nat.card (Z1 ρS) * archH0Card S ρS c ≤ Nat.card M ^ (r + 2 + g + Module.finrank ℚ F) :=
    hb.trans (Nat.pow_le_pow_right hM (by omega))
  refine ⟨CardLe.of_injective ⟨hZ, le_trans (Nat.le_mul_of_pos_right _ ?_) hb'⟩ f hinj, fun hF hcc => ?_⟩
  · unfold archH0Card
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (pow_pos hM _)
    haveI : Nonempty {m : M // ρS (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  · have ha : archH0Card S ρS c = Nat.card M ^ Module.finrank ℚ F := by
      rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
        Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w]
      have hw : ∀ w, Nat.card {m : M // ρS (toGS Ω _ (c w)) m = m} = Nat.card M := fun w => by
        obtain ⟨j, hj, -⟩ := hc w (IsTotallyReal.isReal w)
        exact Nat.card_congr (Equiv.subtypeUnivEquiv fun m => by rw [h1, hρ', hcc _ ⟨j, hj⟩])
      rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ,
        IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    rw [ha, pow_add _ (r + 2 + g)] at hb'
    exact CardLe.of_injective ⟨hZ, Nat.le_of_mul_le_mul_right hb' (pow_pos hM _)⟩ f hinj
