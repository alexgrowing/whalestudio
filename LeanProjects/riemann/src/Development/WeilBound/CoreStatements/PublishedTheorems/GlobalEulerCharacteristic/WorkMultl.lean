import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioOneKilled
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GsEulerRatioShortExactOfBijective
import GroundTheory.ProfiniteCohomology.PoitouTate.NonemptyOfNatCastMemOfNeOne

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_multl

theorem exists_card_eq_pow {ℓ : ℕ} [Fact ℓ.Prime] {X : Type*} [AddCommGroup X] [Finite X] {r : ℕ}
    (h : ∀ m : X, (ℓ ^ r) • m = 0) : ∃ n : ℕ, Nat.card X = ℓ ^ n := by
  have hp : IsPGroup ℓ (Multiplicative X) := fun g => ⟨r, by
    show Multiplicative.toAdd (g ^ (ℓ ^ r)) = Multiplicative.toAdd 1
    rw [toAdd_pow]; exact h _⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  exact ⟨n, by rw [← hn]; rfl⟩

theorem ratio_shortExact_l (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSl : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (T : ShortComplex (Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)))
    (hT : T.ShortExact) [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] [Finite T.X₂]
    (hl : ∃ r : ℕ, ∀ m : T.X₂, (ℓ ^ r) • m = 0) :
    haveI : Finite S := hS
    gsEulerRatio S T.X₂ ιr = gsEulerRatio S T.X₁ ιr * gsEulerRatio S T.X₃ ιr := by
  haveI : Finite S := hS
  haveI : Fintype S := Fintype.ofFinite S
  have hℓ : ℓ.Prime := Fact.out
  haveI : Nonempty S := nonempty_of_natCast_mem_of_ne_one (N := ℓ) S hℓ.one_lt.ne' hSl
  obtain ⟨r, hr⟩ := hl
  have hinj : Function.Injective T.f.hom := (Rep.mono_iff_injective _).1 hT.mono_f
  have hsurj : Function.Surjective T.g.hom := (Rep.epi_iff_surjective _).1 hT.epi_g
  haveI : Finite T.X₁ := Finite.of_injective _ hinj
  haveI : Finite T.X₃ := Finite.of_surjective _ hsurj
  haveI : NeZero (ℓ ^ r) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hSN : ∀ v : HeightOneSpectrum (𝓞 K.1), (((ℓ ^ r : ℕ)) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply hSl v
    rw [Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem r hv
  let ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[K.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) := fun v =>
    (nonempty_algHom_of_isSepClosed : Nonempty (AlgebraicClosure ℚ →ₐ[K.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).some
  have h1 : ∀ m : T.X₁, (ℓ ^ r) • m = 0 := fun m => hinj (by
    rw [map_nsmul, hr, map_zero])
  have hA := bijective_gsRealRes (S := S) (ιr := ιr) (ιs := ιs) (hS := hSN) (M := T.X₁) (hM := h1)
    (r := 3) le_rfl
  have hB := bijective_gsRealRes (S := S) (ιr := ιr) (ιs := ιs) (hS := hSN) (M := T.X₂) (hM := hr)
    (r := 3) le_rfl
  obtain ⟨n, hn⟩ := exists_card_eq_pow hr
  have hn' : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card T.X₂ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply hSl v
    rw [hn, Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem n hv
  exact gsEulerRatio_shortExact_of_bijective S ιr hT hn' hA hB

end PositivityTheory.Lit1.GEN.W_multl
