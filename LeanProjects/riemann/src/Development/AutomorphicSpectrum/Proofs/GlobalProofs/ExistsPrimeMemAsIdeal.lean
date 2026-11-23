import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohFin
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DecompositionGroupMulEquivLocalGaloisCyclotomic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaD

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.GaloisCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem exists_prime_mem_asIdeal {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal :=
  _root_.Bl.FirstLemmaD.goal1 v

theorem finCd2_GK (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R (GK p K) M) (hrho : ContAction rho) :
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧
      ∀ n, 3 ≤ n → Subsingleton (Hn rho n) := by
  obtain ⟨hsep, _, _, hloc, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have : CharZero K := algebraRat.charZero K
  obtain ⟨A, _, e, he⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep (GK p K) R M rho hrho
  have : Finite A := Finite.of_equiv _ e.toEquiv
  have hn : ((Nat.card A : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  obtain ⟨e0, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc0 (GK p K) R M rho A e he
  obtain ⟨e1, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 (GK p K) R M rho A e he
  obtain ⟨e2, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (GK p K) R M rho A e he
  have := finite_cohomology_localField A hn 0
  have := finite_cohomology_localField A hn 1
  have := finite_cohomology_localField A hn 2
  refine ⟨Finite.of_equiv _ e0.symm.toEquiv, Finite.of_equiv _ e1.symm.toEquiv,
    Finite.of_equiv _ e2.symm.toEquiv, fun n h => ?_⟩
  obtain ⟨en⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcn (GK p K) R M rho A e he n
  have := subsingleton_cohomology_localField A hn n h
  exact en.toEquiv.subsingleton

theorem localFiniteness : ReciprocityTheory.Gal.LocalFiniteness := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v _ hA hc
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_asIdeal v
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, e, he, he', -⟩ := GlobalTheory.DecLocal.exists_mulEquiv_cyc F Ω p v A hpv hA
  let E : GK p K ≃ₜ* Dec (F := F) A :=
    { e.symm with continuous_toFun := he', continuous_invFun := he }
  have h : ReciprocityTheory.Neutral.Bridge.FinCd2 (rho.comp (E : GK p K →* Dec (F := F) A)) :=
    finCd2_GK p K hK _ M _ (ReciprocityTheory.Neutral.Bridge.contAction_comp E hc)
  exact ReciprocityTheory.Neutral.Bridge.FinCd2.of_comp E h

end GlobalTheory.CompanionTheory.Hypotheses₂
