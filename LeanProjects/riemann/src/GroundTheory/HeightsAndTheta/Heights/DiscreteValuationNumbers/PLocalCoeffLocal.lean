import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Length
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI

universe u

theorem mem_minimalPrimes_of_locCycle_ne_zero' {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dif_neg hc])

theorem LocalCoeffLocal.proof (h₁ : LocCycleSpanMul.Statement.{u}) (h₂ : LocCyclePos.Statement.{u})
    (h₃ : MinimalPrimesSpanSingleton.Statement.{u}) (h₄ : LocalDomainDimTwo.Statement.{u})
    (h₅ : DimTwoSumReading.Statement.{u}) : LocalCoeffLocal.Statement.{u} := by
  intro A _ _ _ _ hchain f g s u v hf hg hs hu huv hno

  have hv : v ≠ 0 := by
    rintro rfl
    rw [zero_mul] at huv
    exact hf ((IsUnit.mul_right_eq_zero hu).mp huv)
  have hspan : Ideal.span {f} = Ideal.span {v * g} := by
    rw [← huv]
    exact (Ideal.span_singleton_mul_left_unit hu f).symm
  have hcolon : (Ideal.span {f}).colon {g} = Ideal.span {v} := by
    ext x
    rw [hspan, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton, mul_dvd_mul_iff_right hg]
  have hadd : ∀ W : Ideal A, locCycle (Ideal.span {f}) W =
      locCycle (Ideal.span {v}) W + locCycle (Ideal.span {g}) W := by
    intro W
    rw [hspan]
    exact h₁ A v g hv hg W

  have hmin1 : ∀ x : A, x ≠ 0 → ∀ W : Ideal A, locCycle (Ideal.span {x}) W ≠ 0 →
      W.IsPrime ∧ W.height = 1 ∧ x ∈ W :=
    fun x hx W h => (h₃ A x hx W).mp (mem_minimalPrimes_of_locCycle_ne_zero' h)
  have hpos : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, p.IsPrime → p.height = 1 → x ∈ p →
      locCycle (Ideal.span {x}) p ≠ 0 :=
    fun x hx p hp h1 hxp => (h₂ A _ p ((h₃ A x hx p).mpr ⟨hp, h1, hxp⟩)).ne'

  have nb : ∀ p : Ideal A, p.IsPrime → p.height = 1 → v ∈ p → s ∉ p := by
    intro p hp h1 hvp hsp
    have e := hno p (hpos s hs p hp h1 hsp)
    rw [hadd] at e
    exact hpos v hv p hp h1 hvp (by omega)
  have hne : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, x ∈ p → p ≠ ⊥ :=
    fun x hx p hxp h => hx (by rw [h] at hxp; exact (Submodule.mem_bot A).mp hxp)
  have hL : ∀ G : Ideal A, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
      locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      locCycle (Ideal.span {v}) G * locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) := by
    intro G
    rw [hadd]
    ring
  rw [finsum_congr hL, hcolon]
  by_cases hQ : ∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A
  ·
    obtain ⟨hd, -, hht⟩ := h₄ A hchain hQ
    obtain ⟨n₁, e₁, e₁'⟩ := h₅ A hd v s hv nb
    obtain ⟨n₂, e₂, e₂'⟩ := h₅ A hd s v hs (fun p hp h1 hsp hvp => nb p hp h1 hvp hsp)
    have hlen : Module.length A (A ⧸ Ideal.span {v, s}) ≠ ⊤ := by
      by_cases hvs : Ideal.span {v, s} = ⊤
      · have : Subsingleton (A ⧸ Ideal.span {v, s}) := Ideal.Quotient.subsingleton_iff.mpr hvs
        rw [Module.length_eq_zero]
        exact ENat.zero_ne_top
      · have hvm : v ∈ Ideal.span {v, s} := Ideal.subset_span (Set.mem_insert _ _)
        have hsm : s ∈ Ideal.span {v, s} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
        have hI : IsLocalRing.maximalIdeal A ∈ (Ideal.span {v, s}).minimalPrimes := by
          refine ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hvs⟩, fun Q hQ' hQm => ?_⟩
          obtain ⟨hQp, hQI⟩ := hQ'
          by_contra hmQ
          have hlt : Q < IsLocalRing.maximalIdeal A := lt_of_le_of_ne hQm fun h => hmQ h.ge
          have h0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr (hne v hv Q (hQI hvm))
          exact nb Q hQp (hht Q hQp h0 hlt) (hQI hvm) (hQI hsm)
        have : IsArtinianRing (A ⧸ Ideal.span {v, s}) :=
          IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
        have : IsArtinian A (A ⧸ Ideal.span {v, s}) :=
          isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := Ideal.span {v, s}))
        exact Module.length_ne_top
    have key := (lengthFormulaDimTwo A v s hd hv hs hlen).2.2
    rw [e₁', e₂'] at key
    rw [e₁, e₂, Nat.cast_inj.mp key]
  ·
    have hQ' : ∀ Q : Ideal A, Q.IsPrime → Q ≠ ⊥ → Q = IsLocalRing.maximalIdeal A := by
      intro Q hQp h0
      by_contra hQm
      exact hQ ⟨Q, hQp, bot_lt_iff_ne_bot.mpr h0,
        lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQp.ne_top) hQm⟩
    have zl : ∀ G : Ideal A, locCycle (Ideal.span {v}) G *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) = 0 := by
      intro G
      by_contra h
      obtain ⟨hGp, hG1, hvG⟩ := hmin1 v hv G (left_ne_zero_of_mul h)
      have hGm := hQ' G hGp (hne v hv G hvG)
      have hsG : s ∈ G := by
        have h' := (mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2
        rw [← hGm] at h'
        exact h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
      exact nb G hGp hG1 hvG hsG
    have zr : ∀ W : Ideal A, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ Ideal.span {v}) (IsLocalRing.maximalIdeal A) = 0 := by
      intro W
      by_contra h
      obtain ⟨hWp, hW1, hsW⟩ := hmin1 s hs W (left_ne_zero_of_mul h)
      have hWm := hQ' W hWp (hne s hs W hsW)
      have hvW : v ∈ W := by
        have h' := (mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2
        rw [← hWm] at h'
        exact h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self v))
      exact nb W hWp hW1 hvW hsW
    rw [(finsum_congr zl).trans finsum_zero, (finsum_congr zr).trans finsum_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
