import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.DiscreteGroups.GlobalIrreducibility.DzApprox

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

theorem UpperTheory.card_residueField_adicCompletionIntegers_eq_absNorm :
    ∀ {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)),
        Nat.card (IsLocalRing.ResidueField (u.adicCompletionIntegers L)) = normV u := by
  intro L _ _ u
  have hmax : ∀ a : u.adicCompletionIntegers L, a ∈ IsLocalRing.maximalIdeal (u.adicCompletionIntegers L) ↔ Valued.v (a : u.adicCompletion L) < 1 := by
    intro a
    unfold HeightOneSpectrum.adicCompletionIntegers at a ⊢
    exact Valuation.mem_maximalIdeal_iff _ _
  have hval : ∀ x : 𝓞 L, Valued.v ((algebraMap (𝓞 L) (u.adicCompletionIntegers L) x : u.adicCompletionIntegers L) : u.adicCompletion L) < 1 ↔ x ∈ u.asIdeal := by
    intro x
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
    rfl
  let ψ : 𝓞 L →+* IsLocalRing.ResidueField (u.adicCompletionIntegers L) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 L) (u.adicCompletionIntegers L))
  have hker : RingHom.ker ψ = u.asIdeal := by
    ext x
    rw [RingHom.mem_ker]
    show IsLocalRing.residue _ _ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, hmax, hval]
  have hsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    have ha : Valued.v (a : u.adicCompletion L) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp a.2
    obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl u _ ha
    refine ⟨x, ?_⟩
    show IsLocalRing.residue _ _ = _
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmax]
    exact hx
  show Nat.card _ = Nat.card (𝓞 L ⧸ u.asIdeal)
  exact (Nat.card_congr ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).toEquiv).symm
