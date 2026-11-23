import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTopEuler

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.ConjugateSelfDual

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler

open PositivityTheory.LocalTateOrthogonality.Gcoh in

theorem card_H1_eq_card_H0_mul_card_H2 (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (l : ℕ) [hl : Fact l.Prime] (hlp : l ≠ p) (r : ℕ) (M : Type)
    [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK p K) M) (hrho : ContAction rho) :
    Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho) := by
  obtain ⟨hsep, v, t, hloc, hcard⟩ := gcField p K hK
  obtain ⟨A, hA, e, he⟩ := gcRep _ _ M rho hrho
  obtain ⟨e0, -⟩ := gc0 _ _ M rho A e he
  obtain ⟨e1, -⟩ := gc1 _ _ M rho A e he
  obtain ⟨e2, -⟩ := gc2 _ _ M rho A e he
  obtain ⟨k, hk⟩ := exists_card_eq_pow l r M
  have hfA : Finite A := Finite.of_equiv M e.toEquiv
  have hA' : Nat.card A = l ^ k := (Nat.card_congr e.toEquiv).symm.trans hk
  have : CharZero K := algebraRat.charZero K
  have hne : ((Nat.card A : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hE := @card_cohomology_mul_div_eq K (PadicAlgCl p) _ v t hloc _ _ hsep A hA hfA hne
  have hfin := @finite_cohomology_localField K (PadicAlgCl p) _ v t hloc _ _ hsep A hA hfA hne 1
  have hcop : Nat.Coprime (Nat.card A) p := by
    rw [hA']
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes hl.out Fact.out).2 hlp)
  have hu : IsUnit ((Nat.card A : ℕ) : 𝒪[K]) := by
    obtain ⟨a, b, hab⟩ := hcop.cast (R := 𝒪[K])
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact isUnit_of_mul_isUnit_right h
    · exfalso
      have h3 := hcard 1
      rw [pow_one, card_quotient_span_eq_one_of_isUnit (isUnit_of_mul_isUnit_right h)] at h3
      have h4 : 1 < p ^ Module.finrank ℚ_[p] K :=
        Nat.one_lt_pow Module.finrank_pos.ne' (Fact.out : p.Prime).one_lt
      omega
  rw [card_quotient_span_eq_one_of_isUnit hu, Nat.cast_one, inv_one] at hE
  rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv]
  have hp1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_mul]
  exact ((div_eq_one_iff_eq hp1).1 hE).symm

theorem exists_prime_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem localEulerChar_holds : ReciprocityTheory.Gal.LocalEulerChar := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v hr hA hc
  have hval : ∀ (p : ℕ), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → A.valuation (p : Ω) < 1 := fun p hp => by
    simpa using (hA (p : 𝓞 F)).2 hp
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · obtain ⟨K, hK, i0, -, -, hdeg⟩ := GlobalTheory.DecLocal.decEquiv (p := l) (F := F) A (hval l hl)
    let i : ↥(Dec (F := F) A) ≃ₜ* Formalism.GaloisCohomology.GK l K := i0
    let rhoK : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M := rho.comp i.symm.toMulEquiv.toMonoidHom
    have hcomp : ∀ h m, rhoK (i h) m = rho h m := fun h m =>
      congrArg (fun g => rho g m) (i.symm_apply_apply h)
    have hcK : ContAction rhoK := hc.comp' i.symm.continuous
    have h := PositivityTheory.LocalTateOrthogonality.Gcoh.top_euler l K hK r M rhoK hr hcK
    rw [hdeg v hA] at h
    rw [← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH0OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH1OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH2OfIso i rhoK rho hcomp).toEquiv]
    exact h
  · obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
    haveI : Fact p.Prime := ⟨hp⟩
    have hlp : l ≠ p := fun h => hl (h ▸ hpv)
    obtain ⟨K, hK, i0, -, -, -⟩ := GlobalTheory.DecLocal.decEquiv (p := p) (F := F) A (hval p hpv)
    let i : ↥(Dec (F := F) A) ≃ₜ* Formalism.GaloisCohomology.GK p K := i0
    let rhoK : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK p K) M := rho.comp i.symm.toMulEquiv.toMonoidHom
    have hcomp : ∀ h m, rhoK (i h) m = rho h m := fun h m =>
      congrArg (fun g => rho g m) (i.symm_apply_apply h)
    have hcK : ContAction rhoK := hc.comp' i.symm.continuous
    have h := card_H1_eq_card_H0_mul_card_H2 p K hK l hlp r M rhoK hcK
    rw [← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH0OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH1OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH2OfIso i rhoK rho hcomp).toEquiv]
    exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler
