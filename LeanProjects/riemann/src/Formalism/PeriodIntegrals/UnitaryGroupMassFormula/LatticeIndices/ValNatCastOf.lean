import Mathlib
import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit

noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_natCast_of (g : ℕ) (hg1 : (g : 𝓞 F) ∈ v.asIdeal) (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) :
    Valued.v (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) = WithZero.exp (-1 : ℤ) := by
  have h0 : (g : 𝓞 F) ≠ 0 := fun h => hg2 (by rw [h]; exact zero_mem _)
  have key := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (g : 𝓞 F)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at key
  have e : (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) =
      algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F) := by
    rw [map_natCast]
    simp
  rw [e, show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F)) = v.intValuation (g : 𝓞 F) from key]
  have h1 : v.intValuation (g : 𝓞 F) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hg1)
  have h2 : ¬ v.intValuation (g : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => hg2 ((v.intValuation_le_pow_iff_mem _ 2).1 h)
  have hne : v.intValuation (g : 𝓞 F) ≠ 0 := by
    exact v.intValuation_ne_zero _ h0
  rw [← WithZero.exp_log hne] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

theorem resZ_of (g : ℕ) [hgp : Fact g.Prime] (hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = g)
    (hg1 : (g : 𝓞 F) ∈ v.asIdeal) (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) :
    ∃ π : v.adicCompletionIntegers F →+* ZMod g, Function.Surjective π ∧
      RingHom.ker π = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} := by
  have hv := val_natCast_of v g hg1 hg2
  have hmax := ReciprocityTheory.Aut.maxIdeal_eq_span (F := F) (v := v)
    (π := ((g : ℕ) : v.adicCompletionIntegers F)) hv
  have hc : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = g := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, hcard]
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact hgp.out.ne_zero)
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  let e := ZMod.ringEquivOfPrime (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) hgp.out
    (by rw [← Nat.card_eq_fintype_card]; exact hc)
  refine ⟨(e.symm : IsLocalRing.ResidueField (v.adicCompletionIntegers F) →+* ZMod g).comp
    (IsLocalRing.residue _), e.symm.surjective.comp IsLocalRing.residue_surjective, ?_⟩
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.coe_toRingHom, EmbeddingLike.map_eq_zero_iff,
    IsLocalRing.residue_eq_zero_iff, hmax]

end MassDataIdxRes

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

def ResArith {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : Prop :=
  Nat.card (𝓞 X.B.I.F ⧸ p.1.asIdeal) = gOf p ∧ ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal ∧
    ((gOf p : ℕ) : 𝓞 X.B.I.F) ∉ p.1.asIdeal ^ 2

theorem stResZ_of {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) (h : ResArith X p) : StResZ X p := by
  obtain ⟨hc, h1, h2⟩ := h
  have hg0 : gOf p ≠ 0 := by
    intro h0
    apply h2
    rw [h0, Nat.cast_zero]
    exact zero_mem _
  haveI := p.1.isMaximal
  haveI : Finite (𝓞 X.B.I.F ⧸ p.1.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hg0)
  letI : Fintype (𝓞 X.B.I.F ⧸ p.1.asIdeal) := Fintype.ofFinite _
  letI : Field (𝓞 X.B.I.F ⧸ p.1.asIdeal) := Ideal.Quotient.field _
  obtain ⟨n, hl, hcard⟩ := FiniteField.card (𝓞 X.B.I.F ⧸ p.1.asIdeal) (ringChar (𝓞 X.B.I.F ⧸ p.1.asIdeal))
  rw [← Nat.card_eq_fintype_card, hc] at hcard
  have hlP : ((ringChar (𝓞 X.B.I.F ⧸ p.1.asIdeal) : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hn : (n : ℕ) = 1 := by
    by_contra hne
    have h2n : 2 ≤ (n : ℕ) := by
      have := n.pos
      omega
    apply h2
    rw [hcard, Nat.cast_pow]
    exact Ideal.pow_le_pow_right h2n (Ideal.pow_mem_pow hlP n)
  haveI : Fact (gOf p).Prime := ⟨by rw [hcard, hn, pow_one]; exact hl⟩
  exact MassDataIdxRes.resZ_of p.1 (gOf p) hc h1 h2

end MassDataIdxSteps
