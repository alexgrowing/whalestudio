import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFamilyFiniteCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingIso
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P W Q : Ideal A} (hP : P.IsPrime) (hQ : Q.IsPrime) {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P ≤ Q) (hQW : Q ≤ W) : Q = P ∨ Q = W := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hQP, hQW'⟩ := h
  have hWp : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ Q := by rw [Ideal.mk_ker]; exact hPQ
  have hkerW : RingHom.ker f ≤ W := hker.trans hQW
  have : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hkerW
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map f := by
    refine bot_lt_iff_ne_bot.mpr fun h0 => hQP (le_antisymm (fun q hq => ?_) hPQ)
    have hq' : f q ∈ Q.map f := Ideal.mem_map_of_mem f hq
    rw [h0, Ideal.mem_bot] at hq'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq'
  have h2 : Q.map f < W.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun e => hQW' ?_
    have e' := congrArg (Ideal.comap f) e
    rwa [Ideal.comap_map_of_surjective' f hf, Ideal.comap_map_of_surjective' f hf,
      sup_eq_left.mpr hker, sup_eq_left.mpr hkerW] at e'
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have e3 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  rw [Ideal.height_bot] at e1
  have e4 : (0 : ℕ∞) + 1 + 1 ≤ 1 := ((add_le_add e1 le_rfl).trans e2).trans e3
  norm_num at e4

theorem eq_blowUpOf_of_comap_liftForm_le {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {u : J → MRing ι R} {Q : Ideal (MRing (extIdx ι J) R)}
    (hQp : Q.IsPrime) (hQh : IsMultiHomogIdeal Q) (hle : blowUpOf P u ≤ Q) {j : J}
    (hj : (newVar j : MRing (extIdx ι J) R) ∉ Q)
    (hc : Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ P) : Q = blowUpOf P u := by
  classical
  refine le_antisymm (fun F hF => ?_) hle
  have hcomp : ∀ b, weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F ∈ blowUpOf P u := by
    intro b
    set G := weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F
    have hG : IsMultiHomog G b := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hGQ : G ∈ Q := hQh F hF b
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (blowUpEval P u G)
    have hrel : liftForm (u j) ^ (b none) * G - newVar j ^ (b none) * liftForm f ∈ blowUpOf P u := by
      rw [blowUpOf, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow,
        aeval_blowUpSubst_of_isMultiHomog P u hG, aeval_blowUpSubst_liftForm, aeval_blowUpSubst_liftForm,
        aeval_blowUpSubst_newVar, ← hf]
      ring
    have h1 : newVar j ^ (b none) * liftForm f ∈ Q := by
      have h := Q.sub_mem (Q.mul_mem_left (liftForm (u j) ^ (b none)) hGQ) (hle hrel)
      rwa [sub_sub_cancel] at h
    have h2 : liftForm f ∈ Q :=
      (hQp.mem_or_mem h1).resolve_left fun h => hj (hQp.mem_of_pow_mem _ h)
    have h3 : f ∈ P := hc h2
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_of_isMultiHomog P u hG, ← hf,
      Ideal.Quotient.eq_zero_iff_mem.mpr h3, map_zero, zero_mul]
  rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) F]
  exact finsum_induction (· ∈ blowUpOf P u) (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) hcomp

theorem BlowUpOverLocFamilyFinite.proof (h₁ : BlowUpOverLocFibreFinite.Statement.{u}) :
    BlowUpOverLocFamilyFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have hPp : P.IsPrime := hP.multiProj.isPrime
  refine ((Set.finite_singleton (blowUpOf P u)).union
    (h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel)).subset ?_
  rintro Q ⟨hQp, hQh, hQr, hQle, hQW⟩
  obtain ⟨hcp, hPc, -, j, hj⟩ := comap_liftForm_facts hQp hQle hQr
  rcases prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span hPp hcp hWmin hPc hQW with h | h
  · exact Or.inl (eq_blowUpOf_of_comap_liftForm_le hQp hQh hQle hj h.le)
  · exact Or.inr ⟨hQp, hQh, hQr, hQle, h⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
