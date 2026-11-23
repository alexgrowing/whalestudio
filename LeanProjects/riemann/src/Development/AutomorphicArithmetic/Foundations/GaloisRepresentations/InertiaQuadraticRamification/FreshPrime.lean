import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private lemma normV_pos' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) : 0 < normV t := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show 0 < Nat.card (𝓞 F ⧸ t.asIdeal)
  rw [h]
  exact Nat.pos_of_ne_zero (fun h0 => t.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))

private lemma normV_mem' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) :
    ((normV t : ℕ) : 𝓞 F) ∈ t.asIdeal := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show ((Nat.card (𝓞 F ⧸ t.asIdeal) : ℕ) : 𝓞 F) ∈ t.asIdeal
  rw [h]
  exact Ideal.absNorm_mem _

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshPrime :
    SplitPlace → RootMod → FreshPrime := by
  intro hS hR
  unfold SplitPlace at hS
  unfold RootMod at hR
  unfold FreshPrime
  intro F Ω _ _ _ _ _ U hU T hT n hn
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (((2 * n : ℕ)) : Ω) := ⟨by exact_mod_cast (by omega : 2 * n ≠ 0)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 * n)
  have hroot : ∀ t : HeightOneSpectrum (𝓞 F), ∃ x : Ω, x ^ n = (normV t : Ω) :=
    fun t => IsAlgClosed.exists_pow_nat_eq _ hn
  choose y hy using hroot
  set S : Set Ω := insert ζ (y '' T) with hSeq
  haveI : Finite S := (Set.Finite.insert ζ (hT.image y)).to_subtype
  haveI : FiniteDimensional F (IntermediateField.adjoin F S) :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral)
  set U' : Subgroup (G F Ω) := U ⊓ (IntermediateField.adjoin F S).fixingSubgroup with hU'eq
  have hU' : IsOpen (U' : Set (G F Ω)) := by
    rw [hU'eq, Subgroup.coe_inf]
    exact hU.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hfix : ∀ g : G F Ω, g ∈ U' → ∀ x ∈ S, (g : Ω → Ω) x = x := by
    intro g hg x hx
    have hg2 := (Subgroup.mem_inf.mp hg).2
    exact (mem_fixingSubgroup_iff _).mp hg2 x (IntermediateField.subset_adjoin F S hx)
  have hfinset : ∀ a : 𝓞 F, a ≠ 0 → {w : HeightOneSpectrum (𝓞 F) | a ∈ w.asIdeal}.Finite := by
    intro a ha
    have h0 : Ideal.span {a} ≠ (0 : Ideal (𝓞 F)) := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact ha
    simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors h0
  have hcast : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 F) ≠ 0 := fun m hm => by exact_mod_cast hm
  set B : Set (HeightOneSpectrum (𝓞 F)) :=
    T ∪ (⋃ t ∈ T, {w | ((normV t : ℕ) : 𝓞 F) ∈ w.asIdeal}) ∪ {w | ((2 * n : ℕ) : 𝓞 F) ∈ w.asIdeal}
    with hBeq
  have hB : B.Finite := by
    refine (hT.union (hT.biUnion fun t _ => hfinset _ (hcast _ (normV_pos' t).ne'))).union ?_
    exact hfinset _ (hcast _ (by omega))
  obtain ⟨u, huB, hp, hpu, hpu2, hdec⟩ := hS F Ω U' hU' B hB
  have hdvd_mem : ∀ m : ℕ, normV u ∣ m → ((m : ℕ) : 𝓞 F) ∈ u.asIdeal := by
    rintro m ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hpu
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω u
  have hDA : ∀ x ∈ S, ∀ g ∈ Dec A, (g : Ω → Ω) x = x := fun x hx g hg => hfix g (hdec A hA hg) x hx
  refine ⟨u, fun h => huB (Or.inl (Or.inl h)), hp, hpu, hpu2,
    fun A' hA' => le_trans (hdec A' hA') inf_le_left, ?_, ?_⟩
  · refine (hR F Ω A u hA (normV u) hp rfl ζ (2 * n) (by omega) (hDA ζ (Set.mem_insert _ _))).2 hζ ?_
    intro h2
    exact huB (Or.inr (hdvd_mem _ h2))
  · intro t ht
    refine ⟨?_, (hR F Ω A u hA (normV u) hp rfl (y t) n hn
      (hDA (y t) (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩))).1 (normV t) (hy t)⟩
    intro hut
    by_cases hd : normV u ∣ normV t
    · exact huB (Or.inl (Or.inr (Set.mem_biUnion ht (hdvd_mem _ hd))))
    · have hcop : Nat.Coprime (normV u) (normV t) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hd
      have hg := Nat.gcd_eq_gcd_ab (normV u) (normV t)
      rw [hcop] at hg
      have hg' := congrArg (Int.cast : ℤ → 𝓞 F) hg
      push_cast at hg'
      have h1 : (1 : 𝓞 F) ∈ t.asIdeal := by
        rw [hg']
        exact t.asIdeal.add_mem (Ideal.mul_mem_right _ _ hut) (Ideal.mul_mem_right _ _ (normV_mem' t))
      exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
