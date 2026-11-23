import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreThree

open Formalism.IndefR.Bridge in
theorem conj_ne_of_two {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  have hP' : P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = P.asIdeal := congrArg HeightOneSpectrum.asIdeal hP
  have hfix : ∀ x : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E x ∈ P.asIdeal ↔ x ∈ P.asIdeal := fun x => by
    conv_lhs => rw [← hP']
    exact Ideal.apply_mem_of_equiv_iff
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h2 (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap, ← hfix x]
  refine Eq.to_iff (congrArg (· ∈ P.asIdeal) (RingOfIntegers.ext ?_))
  exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm

theorem exists_two (D : D7) : ∃ P : HeightOneSpectrum (𝓞 D.host.E), ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  haveI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Nat.prime_two).irreducible
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) (Ideal.span {(2 : ℤ)}) (by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := by
      have := congrArg (fun y : 𝓞 D.host.E => ((y : D.host.E))) hx
      simpa using this
    rw [this]; exact zero_mem _)
  have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ Q := by
    have : (2 : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 D.host.E)) := hc ▸ Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun hb => ?_⟩, h2⟩
  rw [hb, Ideal.mem_bot] at h2
  have := congrArg (fun y : 𝓞 D.host.E => ((y : D.host.E))) h2
  norm_num at this

end GlobalTheory.CoreThree

namespace GlobalTheory.CoreThree

theorem heckeCharacterisation_places_parts_of_weak : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toRealDat.ExAt → Core R.toRealDat F.lv2) ∧ IsSF R.toRealDat R.SF ∧ (∀ t, ∀ Q ∈ A3.okI t, Good R.toRealDat t (R.plI Q) ∧ conjPl (R.plI Q) = R.plI Q) ∧ (∀ P, Good R.toRealDat A3.A.μ0 P → (conjPl P = P → ∃ Q ∈ A3.okI A3.A.μ0, R.plI Q = P) ∧ (conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P)) ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ (∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c) ∧ (A3.A.ok A3.A.μ0).Nonempty := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h
  have hL : R.toLevCh.Is A3.A.μ0 := h.base.lev
  obtain ⟨hQ0, -, -, -⟩ := GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hL
  obtain ⟨_, _, _, ht⟩ := h.base.fam.tie
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  have hon : ∀ P, Good R.toRealDat A3.A.μ0 P → (Formalism.DivisionValues.conjPl P = P → ∃ Q ∈ A3.okI A3.A.μ0, R.plI Q = P) ∧
      (Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P) := by
    intro P hP
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hP P (Or.inl hm)).1 rfl
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
        refine ⟨?_, hnS⟩
        rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
      obtain ⟨Q, hQ⟩ := h.inert.onto P hio
      refine ⟨Q, (h.inert.tie.okI A3.A.μ0 Q).2 ?_, hQ⟩
      rw [hQ0, Finset.coe_empty, Set.union_empty, hQ]
      exact hio
    · have hso : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) := by
        refine ⟨?_, hnS, fun Q hQ he => ?_⟩
        · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
          exact fun he => hf (HeightOneSpectrum.ext he)
        · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at he
          have hQP : Q = Formalism.DivisionValues.conjPl P := HeightOneSpectrum.ext he
          rw [hSb] at hQ
          apply (hP Q (Or.inl hQ)).2
          have := GlobalTheory.SplitHeckeAdj.isConjPl_conj (Formalism.DivisionValues.conjPl P)
          rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at this
          rw [hQP]; exact this
      obtain ⟨P0, hP0⟩ := h.base.fam.pl_onto P hso
      refine ⟨P0, (ht.ok A3.A.μ0 P0).2 ?_, hP0⟩
      rw [hQ0, Finset.coe_empty, Set.union_empty, hP0]
      exact hso
  refine ⟨fun e => (GlobalTheory.CoreOfWeak.core_of_weak R F h e).1, ?_, ?_, hon, fun c => rfl, fun i c => rfl, ?_⟩
  · intro v
    rw [h.inert.SF v, h.allPl]
  · intro t Q hQ
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · obtain ⟨P, h2⟩ := exists_two D
    have hg : Good R.toRealDat A3.A.μ0 P := by
      intro PP hPP
      rw [hQ0] at hPP
      have hm : PP ∈ R.Pg := hPP.resolve_right (by simp)
      obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
      have hgk := GlobalTheory.LevelPlaces.mem_of_div _ k PP hk
      have hn : ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
        GlobalTheory.LevelPlaces.not_mem_of_prime PP.isPrime.ne_top Nat.prime_two (D.host.g_prime k) (Formalism.L2.Pj.g_ne_two D k) hgk
      refine ⟨fun he => hn (he ▸ h2), fun hc => ?_⟩
      have hgP := GlobalTheory.LevelPlaces.natCast_mem_of_isConjPl hc hgk
      exact GlobalTheory.LevelPlaces.not_mem_of_prime P.isPrime.ne_top Nat.prime_two (D.host.g_prime k)
        (Formalism.L2.Pj.g_ne_two D k) hgP h2
    obtain ⟨P0, hP0, -⟩ := (hon P hg).2 (conj_ne_of_two P h2)
    exact ⟨P0, hP0⟩

end GlobalTheory.CoreThree
