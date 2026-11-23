import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AutomorphyRankFourPolarizedAlt
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem val_iff_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (p : ℕ) : A.valuation (p : Ω) < 1 ↔ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← hA]
  simp

private theorem prime_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 F ⧸ v.asIdeal), CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem UpperTheory.V.Z.Win.Birth.badOfW :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.SplitOfDec → UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.UnrOfIne → SphOfUnrW → BadOfW := by
  intro hS hU hP Ω _ _ _ l _ ι K' L M _ _ _ _ _ _ _ hM ρ r π hG hr hpol hreg hatt hW hun v hv
  have hMfix : ∀ s : G L Ω, resQ L s ∈ K'.fixingSubgroup → ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := fun s hs x => by
    have : resQ L s ∈ M.fixingSubgroup := by
      rw [hM, IntermediateField.fixingSubgroup_sup]
      exact ⟨hs, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
  obtain ⟨p, hp, hpv⟩ := prime_mem v
  rcases hG p hp with h | ⟨hpl, h⟩
  · exact absurd (hS L M Ω v fun A hA s hs => hMfix s (h A ((val_iff_mem hA p).2 hpv) hs)) hv
  refine ⟨hU L M Ω v fun A hA s hs => hMfix s (h A ((val_iff_mem hA p).2 hpv) s hs).1, fun w hw => ?_⟩
  have hpw : ((p : ℕ) : 𝓞 M) ∈ w.asIdeal := by
    rw [← hw] at hpv
    change algebraMap (𝓞 L) (𝓞 M) p ∈ w.asIdeal at hpv
    rwa [map_natCast] at hpv
  have hlw : ((l : ℕ) : 𝓞 M) ∉ w.asIdeal := fun hl => by
    have hc : IsCoprime ((p : ℕ) : 𝓞 M) ((l : ℕ) : 𝓞 M) :=
      Nat.Coprime.cast ((Nat.coprime_primes hp Fact.out).2 hpl)
    obtain ⟨a, b, e⟩ := hc
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hpw) (w.asIdeal.mul_mem_left b hl)))
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  refine hP M Ω l ι 2 one_le_two r π hr hpol hreg hatt hW w hlw A hA fun s hs => ?_
  exact hun A (mt (val_iff_mem hA l).1 hlw) s hs (h A ((val_iff_mem hA p).2 hpw) (galEmb L M Ω s) ⟨hs.1, hs.2⟩).2
