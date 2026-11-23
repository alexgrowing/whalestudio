import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivisorIdealBotUniformiser
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section General

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem idealCycle_eq_of_mul_mem {J J' U : Ideal (MRing ι R)} {s t : MRing ι R} (hs : s ∉ U)
    (ht : t ∉ U) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    idealCycle J U = idealCycle J' U := by
  unfold idealCycle
  by_cases h : U ∈ J.minimalPrimes ∧ IsRelevant U
  · have h' : U ∈ J'.minimalPrimes ∧ IsRelevant U :=
      ⟨mem_minimalPrimes_of_mul_mem hs ht hsJ htJ h.1, h.2⟩
    rw [dif_pos h, dif_pos h']
    have : U.IsPrime := h.1.1.1
    unfold multAt
    rw [length_localized_eq_of_mul_mem hs ht hsJ htJ]
  · have h' : ¬ (U ∈ J'.minimalPrimes ∧ IsRelevant U) := fun h' =>
      h ⟨mem_minimalPrimes_of_mul_mem ht hs htJ hsJ h'.1, h'.2⟩
    rw [dif_neg h, dif_neg h']

theorem divCycle_eq_zero_of_not_mem {W U : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ U) :
    divCycle W x U = 0 := by
  unfold divCycle
  rw [dif_neg]
  rintro ⟨h, -⟩
  exact hx (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end General

theorem DivisorIdealCycle.proof : DivisorIdealCycle.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W f g u v hP hW hPW hg hloc hu hv huv
  funext U
  by_cases hU : U.IsPrime ∧ W ≤ U ∧ IsRelevant U
  · obtain ⟨hUp, hWU, hUrel⟩ := hU
    obtain ⟨u', v', hu'U, hloc'⟩ := hloc U hUp hWU hUrel
    have hu'W : u' ∉ W := fun h => hu'U (hWU h)
    have h1U : (1 : MRing ι R) ∉ U := (Ideal.ne_top_iff_one U).mp hUp.ne_top

    have hcross : u * v' - u' * v ∈ P := by
      have hmem : (u * v' - u' * v) * g ∈ P := by
        rw [show (u * v' - u' * v) * g = u' * (u * f - v * g) - u * (u' * f - v' * g) by ring]
        exact P.sub_mem (P.mul_mem_left _ huv) (P.mul_mem_left _ hloc')
      exact (hP.mem_or_mem hmem).resolve_right hg
    have hv'W : v' ∉ W := by
      intro h
      have hmem : u' * v ∈ W := by
        rw [show u' * v = u * v' - (u * v' - u' * v) by ring]
        exact W.sub_mem (W.mul_mem_left u h) (hPW hcross)
      exact (hW.mem_or_mem hmem).elim hu'W hv

    have hmul := congrFun (DivCycleMul.proof R K ι W u' v hW hu'W hv) U
    have hmul' := congrFun (DivCycleMul.proof R K ι W u v' hW hu hv'W) U
    have heq : divCycle W (u' * v) U = divCycle W (u * v') U :=
      divCycle_eq_of_mul_sub_mem (P := W) (W := U) (u := 1) (v := 1) h1U h1U (by
        rw [show 1 * (u' * v) - 1 * (u * v') = -(u * v' - u' * v) by ring]
        exact W.neg_mem (hPW hcross))
    have hu'0 : divCycle W u' U = 0 := divCycle_eq_zero_of_not_mem hu'U
    simp only [Pi.add_apply] at hmul hmul'

    have hv'D : v' ∈ divisorIdeal P f g := by
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul,
        show v' * g = u' * f - (u' * f - v' * g) by ring]
      exact Submodule.sub_mem _
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)))
        (Ideal.mem_sup_left hloc')
    have hsJ : ∀ x ∈ W ⊔ Ideal.span {v'}, 1 * x ∈ W ⊔ divisorIdeal P f g := by
      intro x hx
      rw [one_mul]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hv'D) W hx
    have htJ : ∀ x ∈ W ⊔ divisorIdeal P f g, u' * x ∈ W ⊔ Ideal.span {v'} := by
      intro x hx
      obtain ⟨w, hw, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul] at hd
      obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hd
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      have h1 : (u' * d - a * v') * g ∈ P := by
        have e : (u' * d - a * v') * g = u' * p + a * (u' * f - v' * g) := by
          calc (u' * d - a * v') * g = u' * (d * g) - a * v' * g := by ring
            _ = u' * p + a * (u' * f - v' * g) := by rw [← hpr]; ring
        rw [e]
        exact P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hloc')
      have h2 : u' * d - a * v' ∈ P := (hP.mem_or_mem h1).resolve_right hg
      rw [show u' * (w + d) = (u' * w + (u' * d - a * v')) + a * v' by ring]
      exact Submodule.add_mem_sup (W.add_mem (W.mul_mem_left _ hw) (hPW h2))
        (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
    have hR : idealCycle (W ⊔ divisorIdeal P f g) U = divCycle W v' U := by
      rw [divCycle_eq_idealCycle]
      exact (idealCycle_eq_of_mul_mem h1U hu'U hsJ htJ).symm
    rw [hR]
    show divCycle W v U - divCycle W u U = divCycle W v' U
    omega
  · have hcomp : ∀ J : Ideal (MRing ι R), W ≤ J → ¬ (U ∈ J.minimalPrimes ∧ IsRelevant U) := by
      rintro J hWJ ⟨h, hrel⟩
      exact hU ⟨h.1.1, hWJ.trans h.1.2, hrel⟩
    show divCycle W v U - divCycle W u U = idealCycle (W ⊔ divisorIdeal P f g) U
    unfold divCycle idealCycle
    rw [dif_neg (hcomp _ le_sup_left), dif_neg (hcomp _ le_sup_left), dif_neg (hcomp _ le_sup_left),
      sub_self]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
