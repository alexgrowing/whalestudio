import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.HostCM

theorem valuation_eq_of_unram (K : Type) [Field K] [NumberField K] [IsCMField K]
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : HeightOneSpectrum (𝓞 K)) (x : maximalRealSubfield K) :
    P.valuation K (algebraMap (maximalRealSubfield K) K x) =
      (P.under (𝓞 (maximalRealSubfield K))).valuation (maximalRealSubfield K) x := by
  have hp := P.isPrime
  have hp' := (P.under (𝓞 (maximalRealSubfield K))).isPrime
  have : P.asIdeal.LiesOver (P.under (𝓞 (maximalRealSubfield K))).asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[maximalRealSubfield K] K)
    (P.under (𝓞 (maximalRealSubfield K))).asIdeal P.asIdeal
  have h1 : Nat.card (P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩
    have key : ∀ z : P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K),
        (z : K ≃ₐ[maximalRealSubfield K] K) = 1 := by
      intro z
      rcases Eta.cases K z.1 with hz | hz
      · exact hz
      · exfalso
        have hm := AddSubgroup.mem_inertia.mp z.2
        rw [hz] at hm
        exact hunr P.asIdeal hp P.ne_bot hm
    rw [key x, key y]
  rw [h1, Ideal.ramificationIdxIn_eq_ramificationIdx _ P.asIdeal (K ≃ₐ[maximalRealSubfield K] K)] at hcard
  rw [← HeightOneSpectrum.valuation_liesOver K (P.under (𝓞 (maximalRealSubfield K))) P x,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (P.under (𝓞 (maximalRealSubfield K))).ne_bot, ← hcard, pow_one]

open Classical in

theorem host_cm_embedding_properties : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ (IsTotallyReal H.F ∧ IsTotallyComplex H.E ∧ Module.finrank H.F H.E = 2 ∧ c ≠ 1 ∧ Function.Bijective fun g => InfinitePlace.mk (embPsi H g)) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), ordF P (upF H.F k) = ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  have hmem : ∀ g : R.Psi, embPsi H g ∈ H.cmType := fun g => ((factEmb R H).2 g).2 g.2
  have hT := H.der.cmType.1
  refine ⟨IsCMField.complexConj H.E, hc, ⟨inferInstance, inferInstance,
    Algebra.IsQuadraticExtension.finrank_eq_two _ _, IsCMField.complexConj_ne_one _,
    ?_, ?_⟩, ?_, hmem, ?_⟩
  · intro g g' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact Subtype.ext ((factEmb R H).1.1 h)
    · have h' := hmem g'
      rw [← h] at h'
      exact absurd h' ((hT _).1 (hmem g))
  · intro w
    by_cases hw : w.embedding ∈ H.cmType
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 w.embedding
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw)⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_embedding]
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 (ComplexEmbedding.conjugate w.embedding)
      have hw' : ComplexEmbedding.conjugate w.embedding ∈ H.cmType := by
        by_contra h'
        exact hw ((hT _).2 h')
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw')⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  · intro P k
    have := valuation_eq_of_unram H.E (fun P hP h0 hx => H.der.unramEF P hP h0 fun x => by
      have e : H.conj • x = IsCMField.complexConj H.E • x := Subtype.ext (hc x).symm
      rw [e]
      exact hx x) P k
    unfold ordF
    rw [← this]
    rfl
  · rw [← Nat.card_eq_fintype_card]
    exact (factCardPsi R H).1

open Classical in

theorem host_cm : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ CMData H.F c (embPsi H) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), ordF P (upF H.F k) = ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  obtain ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩ := host_cm_embedding_properties R H
  exact ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩

end GlobalTheory.Mem.HostCM
