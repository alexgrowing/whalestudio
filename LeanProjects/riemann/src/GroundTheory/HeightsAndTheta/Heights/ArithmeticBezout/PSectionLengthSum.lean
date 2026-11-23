import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionLengthSum
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLocalSectionLengthSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace SectionLengthSum

theorem prime_between {A : Type*} [CommRing A] [IsNoetherianRing A] {J W Q : Ideal A} {f : A}
    (hWP : ∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    [hQ : Q.IsPrime] (hJQ : J ≤ Q) (hQW : Q ≤ W) : Q ∈ J.minimalPrimes ∨ Q = W := by
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hPp : P.IsPrime := hP.1.1
  rcases eq_or_lt_of_le hPQ with h | hlt
  · exact Or.inl (h ▸ hP)
  rcases eq_or_lt_of_le hQW with h | hlt2
  · exact Or.inr h
  exfalso
  have hW := hWP P hP (hPQ.trans hQW)
  have hWp : W.IsPrime := hW.1.1
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  set g := Ideal.Quotient.mk P
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = P := Ideal.mk_ker
  have hcm : ∀ I : Ideal A, P ≤ I → (I.map g).comap g = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective g hsurj, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hI]
  have : (Q.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ)
  have : (W.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ.trans hQW)
  have : (W.map g).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have : (Q.map g).FiniteHeight :=
    ⟨Or.inr ((Ideal.height_mono (Ideal.map_mono hQW)).trans_lt (h1.trans_lt (WithTop.coe_lt_top 1))).ne⟩
  have hbot : (⊥ : Ideal (A ⧸ P)) < Q.map g := by
    refine lt_of_le_of_ne bot_le fun h => hlt.ne ?_
    rw [← hcm Q hPQ, ← h, ← RingHom.ker_eq_comap_bot, hker]
  have hQW' : Q.map g < W.map g := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun h => hlt2.ne ?_
    rw [← hcm Q hPQ, h, hcm W (hPQ.trans hQW)]
  have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hQW'
  have h3 := Ideal.height_strict_mono_of_isPrime_of_isPrime (I := ⊥) hbot
  have h4 : (Q.map g).height < 1 := h2.trans_le h1
  rw [Order.lt_one_iff] at h4
  rw [h4] at h3
  exact absurd h3 (not_lt_of_ge bot_le)

theorem length_ne_top_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (I : Ideal B) (hI : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes) : Module.length B (B ⧸ I) ≠ ⊤ := by
  have : IsArtinianRing (B ⧸ I) := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian B (B ⧸ I) := isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

theorem proof (hLoc : LocalSectionLengthSum.Statement) : SectionLengthSum.Statement := by
  intro A _ _ J W f hJ hf hW hWP
  classical
  have hWp : W.IsPrime := hW.1.1
  let B := Localization.AtPrime W
  let φ := algebraMap A B
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing W.primeCompl B inferInstance
  have hmin : ∀ Q : Ideal B, Q ∈ (J.map φ).minimalPrimes ↔ Q.comap φ ∈ J.minimalPrimes := fun Q => by
    rw [IsLocalization.minimalPrimes_map W.primeCompl B J]
    rfl
  have hcomapW : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ ≤ W := fun Q hQ x hx => by
    by_contra hxW
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units B (⟨x, hxW⟩ : W.primeCompl)))
  have hmapcomap : ∀ Q : Ideal B, (Q.comap φ).map φ = Q := fun Q =>
    IsLocalization.map_under W.primeCompl B Q
  have hcomapmap : ∀ P : Ideal A, P.IsPrime → P ≤ W → (P.map φ).comap φ = P := fun P hP hPW =>
    IsLocalization.under_map_of_isPrime_disjoint W.primeCompl B hP
      (Set.disjoint_left.mpr fun x hx hxP => hx (hPW hxP))
  have hJ' : (J.map φ).IsRadical := by
    show (J.map φ).radical ≤ J.map φ
    rw [← IsLocalization.map_radical W.primeCompl B J, hJ.radical]
  have hf' : ∀ Q ∈ (J.map φ).minimalPrimes, φ f ∉ Q := fun Q hQ hfQ => hf _ ((hmin Q).1 hQ) hfQ
  have hdim : ∀ Q : Ideal B, Q.IsPrime → J.map φ ≤ Q →
      Q ∈ (J.map φ).minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B := by
    intro Q hQ hJQ
    have : (Q.comap φ).IsPrime := hQ.comap φ
    rcases prime_between hWP (Ideal.map_le_iff_le_comap.mp hJQ) (hcomapW Q hQ) with h | h
    · exact Or.inl ((hmin Q).2 h)
    · right
      rw [← hmapcomap Q, h]
      exact IsLocalization.AtPrime.map_eq_maximalIdeal W B
  have key := hLoc B (J.map φ) (φ f) hJ' hf' hdim
  have hsup : ∀ I : Ideal A, (I ⊔ Ideal.span {f}).map φ = I.map φ ⊔ Ideal.span {φ f} := fun I => by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hlm : ∀ I : Ideal A, localMult (I ⊔ Ideal.span {f}) W =
      (Module.length B (B ⧸ (I.map φ ⊔ Ideal.span {φ f}))).toNat := fun I => by
    unfold localMult
    rw [dif_pos hWp, hsup]
  have hfW : φ f ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W B]
    exact Ideal.mem_map_of_mem φ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
  have hfin : ∀ Q ∈ (J.map φ).minimalPrimes,
      Module.length B (B ⧸ (Q ⊔ Ideal.span {φ f})) ≠ ⊤ := by
    intro Q hQ
    refine length_ne_top_of_mem_minimalPrimes _ ⟨⟨(IsLocalRing.maximalIdeal.isMaximal B).isPrime,
      sup_le (IsLocalRing.le_maximalIdeal hQ.1.1.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hfW)⟩,
      fun Q₂ hQ₂ _ => ?_⟩
    rcases hdim Q₂ hQ₂.1 (hQ.1.2.trans (le_sup_left.trans hQ₂.2)) with h | h
    · exact absurd (hQ₂.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) (hf' Q₂ h)
    · exact h.ge
  rw [hlm J, key, ENat.toNat_sum (fun Q hQ => hfin Q ((Set.Finite.mem_toFinset _).mp hQ))]
  symm
  refine Finset.sum_nbij' (fun P => P.map φ) (fun Q => Q.comap φ) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    rw [Set.Finite.mem_toFinset, hmin, hcomapmap P hP.1.1.1 hP.2]
    exact hP.1
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨(hmin Q).1 hQ, hcomapW Q hQ.1.1⟩
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    exact hcomapmap P hP.1.1.1 hP.2
  · intro Q _
    exact hmapcomap Q
  · intro P _
    exact hlm P

end SectionLengthSum

end GroundTheory.Heights₂.Heights
