import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section BlowUpLocRingInj

variable {R : Type*} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type} {J : Type}

theorem blowUpSubst_eq_C_mul_X_pow (P : Ideal (MRing ι R)) (u : J → MRing ι R) (v : Σ o, extIdx ι J o) :
    blowUpSubst P u v =
      Polynomial.C (blowUpEval P u (X v)) * Polynomial.X ^ (blockWeight (extIdx ι J) v none) := by
  obtain ⟨(_ | k), i⟩ := v
  · simp [blowUpSubst, blowUpEval, blockWeight]
  · simp [blowUpSubst, blowUpEval, blockWeight]

theorem aeval_blowUpSubst_monomial (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    (d : (Σ o, extIdx ι J o) →₀ ℕ) (c : R) :
    aeval (blowUpSubst P u) (monomial d c) =
      Polynomial.C (blowUpEval P u (monomial d c)) *
        Polynomial.X ^ (Finsupp.weight (blockWeight (extIdx ι J)) d none) := by
  have key : ∃ q, aeval (blowUpSubst P u) (monomial d c) =
      Polynomial.C q * Polynomial.X ^ (Finsupp.weight (blockWeight (extIdx ι J)) d none) := by
    refine ⟨algebraMap R _ c * ∏ v ∈ d.support, blowUpEval P u (X v) ^ d v, ?_⟩
    have hp : ∀ (y : MRing ι R ⧸ P) (e k : ℕ),
        (Polynomial.C y * Polynomial.X ^ e) ^ k = Polynomial.C (y ^ k) * Polynomial.X ^ (e * k) := by
      intro y e k
      rw [map_pow, pow_mul]
      ring
    rw [aeval_monomial, Polynomial.algebraMap_apply, Finsupp.prod]
    simp_rw [blowUpSubst_eq_C_mul_X_pow, hp]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul]
    refine congrArg₂ (· * ·) rfl (congrArg _ ?_)
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [mul_comm]
  obtain ⟨q, hq⟩ := key
  rw [hq]
  congr 2
  change q = Polynomial.eval 1 (aeval (blowUpSubst P u) (monomial d c))
  rw [hq]
  simp

theorem aeval_blowUpSubst_eq_C_blowUpEval_mul_X_pow (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    {G : MRing (extIdx ι J) R} {b : Option K → ℕ} (hG : IsMultiHomog G b) :
    aeval (blowUpSubst P u) G = Polynomial.C (blowUpEval P u G) * Polynomial.X ^ b none := by
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_blowUpSubst_monomial, hG (mem_support_iff.mp hd)]

theorem mem_blowUpOf_of_isMultiHomog {P : Ideal (MRing ι R)} {u : J → MRing ι R}
    {G : MRing (extIdx ι J) R} {b : Option K → ℕ} (hG : IsMultiHomog G b) (h : blowUpEval P u G = 0) :
    G ∈ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_eq_C_blowUpEval_mul_X_pow P u hG, h, map_zero, zero_mul]

theorem algebraMap_blowUpEval_ne_zero {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q : Ideal (MRing (extIdx ι J) R)} (hle : blowUpOf P u ≤ Q) {G : MRing (extIdx ι J) R}
    {b : Option K → ℕ} (hG : IsMultiHomog G b) (hGQ : G ∉ Q) :
    algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G) ≠ 0 := by
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact fun h => hGQ (hle (mem_blowUpOf_of_isMultiHomog hG h))

theorem exists_eq_div_of_mem_blowUpLocRing {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime) (hle : blowUpOf P u ≤ Q)
    {z : FractionRing (MRing ι R ⧸ P)} (hz : z ∈ blowUpLocRing P u Q) :
    ∃ (b : Option K → ℕ) (F G : MRing (extIdx ι J) R), IsMultiHomog F b ∧ IsMultiHomog G b ∧ G ∉ Q ∧
      z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
        algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G) := by
  have h1 : (1 : MRing (extIdx ι J) R) ∉ Q := fun h => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  induction hz using Subring.closure_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, 0, 1, isWeightedHomogeneous_zero R _ _, isWeightedHomogeneous_one R _, h1, by simp⟩
  | one =>
    exact ⟨0, 1, 1, isWeightedHomogeneous_one R _, isWeightedHomogeneous_one R _, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b₁, F₁, G₁, hF₁, hG₁, hG₁Q, rfl⟩ := hx
    obtain ⟨b₂, F₂, G₂, hF₂, hG₂, hG₂Q, rfl⟩ := hy
    refine ⟨b₁ + b₂, F₁ * G₂ + G₁ * F₂, G₁ * G₂,
      IsWeightedHomogeneous.add (IsWeightedHomogeneous.mul hF₁ hG₂) (IsWeightedHomogeneous.mul hG₁ hF₂),
      IsWeightedHomogeneous.mul hG₁ hG₂, fun h => (hQ.mem_or_mem h).elim hG₁Q hG₂Q, ?_⟩
    rw [div_add_div _ _ (algebraMap_blowUpEval_ne_zero hle hG₁ hG₁Q)
      (algebraMap_blowUpEval_ne_zero hle hG₂ hG₂Q)]
    simp only [map_add, map_mul]
  | neg x _ hx =>
    obtain ⟨b, F, G, hF, hG, hGQ, rfl⟩ := hx
    refine ⟨b, -F, G, fun d hd => hF (by rwa [coeff_neg, neg_ne_zero] at hd), hG, hGQ, ?_⟩
    rw [map_neg, map_neg, neg_div]
  | mul x y _ _ hx hy =>
    obtain ⟨b₁, F₁, G₁, hF₁, hG₁, hG₁Q, rfl⟩ := hx
    obtain ⟨b₂, F₂, G₂, hF₂, hG₂, hG₂Q, rfl⟩ := hy
    refine ⟨b₁ + b₂, F₁ * F₂, G₁ * G₂, IsWeightedHomogeneous.mul hF₁ hF₂,
      IsWeightedHomogeneous.mul hG₁ hG₂, fun h => (hQ.mem_or_mem h).elim hG₁Q hG₂Q, ?_⟩
    rw [div_mul_div_comm]
    simp only [map_mul]

theorem exists_monomial_not_mem_of_isMultiHomog {Q : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime)
    (hrel : IsRelevant Q) {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b)
    (hF0 : F ≠ 0) : ∃ M : MRing (extIdx ι J) R, IsMultiHomog M b ∧ M ∉ Q := by
  classical
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hF0
  choose i hi using hrel
  let e := Finsupp.mapDomain (fun v : Σ o, extIdx ι J o => (⟨v.1, i v.1⟩ : Σ o, extIdx ι J o)) d
  refine ⟨monomial e 1, isWeightedHomogeneous_monomial _ _ _ ?_, fun hmem => ?_⟩
  · rw [← hF hd]
    change Finsupp.linearCombination ℕ _ e = Finsupp.linearCombination ℕ _ d
    rw [Finsupp.linearCombination_mapDomain]
    rfl
  · have hmon : (monomial e 1 : MRing (extIdx ι J) R) ∈ Q.primeCompl := by
      rw [monomial_eq, map_one, one_mul, Finsupp.prod]
      refine prod_mem fun v hv => pow_mem ?_ _
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
      exact hi w.1
    exact hmon hmem

theorem mem_of_blowUpLocRing_le {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q Q' : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime) (hrel : IsRelevant Q)
    (hle : blowUpOf P u ≤ Q) (hle' : blowUpOf P u ≤ Q')
    (hsub : blowUpLocRing P u Q' ≤ blowUpLocRing P u Q) {F : MRing (extIdx ι J) R} {b : Option K → ℕ}
    (hF : IsMultiHomog F b) (hFQ : F ∈ Q) : F ∈ Q' := by
  by_contra hFQ'
  have hF0 : F ≠ 0 := fun h => hFQ' (h ▸ Q'.zero_mem)
  obtain ⟨M, hM, hMQ⟩ := exists_monomial_not_mem_of_isMultiHomog hQ hrel hF hF0
  have hz : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u M) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) ∈
        blowUpLocRing P u Q :=
    hsub (Subring.subset_closure ⟨b, M, F, hM, hF, hFQ', rfl⟩)
  obtain ⟨b₁, F₁, G₁, hF₁, hG₁, hG₁Q, heq⟩ := exists_eq_div_of_mem_blowUpLocRing hQ hle hz
  rw [div_eq_div_iff (algebraMap_blowUpEval_ne_zero hle' hF hFQ')
    (algebraMap_blowUpEval_ne_zero hle hG₁ hG₁Q)] at heq
  have hinj : blowUpEval P u M * blowUpEval P u G₁ = blowUpEval P u F₁ * blowUpEval P u F :=
    IsFractionRing.injective (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (by
      rw [map_mul, map_mul]
      exact heq)
  have h0 : blowUpEval P u (M * G₁ - F * F₁) = 0 := by
    rw [map_sub, map_mul, map_mul, hinj]
    ring
  have hmem : M * G₁ - F * F₁ ∈ Q :=
    hle (mem_blowUpOf_of_isMultiHomog (IsWeightedHomogeneous.sub
      (IsWeightedHomogeneous.mul hM hG₁) (IsWeightedHomogeneous.mul hF hF₁)) h0)
  rw [Submodule.sub_mem_iff_left _ (Q.mul_mem_right F₁ hFQ)] at hmem
  exact (hQ.mem_or_mem hmem).elim hMQ hG₁Q

theorem le_of_blowUpLocRing_le {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q Q' : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime) (hQh : IsMultiHomogIdeal Q)
    (hrel : IsRelevant Q) (hle : blowUpOf P u ≤ Q) (hle' : blowUpOf P u ≤ Q')
    (hsub : blowUpLocRing P u Q' ≤ blowUpLocRing P u Q) : Q ≤ Q' := by
  intro f hf
  rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  exact Q'.sum_mem fun b _ => mem_of_blowUpLocRing_le hQ hrel hle hle' hsub
    (weightedHomogeneousComponent_isWeightedHomogeneous (n := b) (φ := f)) (hQh f hf b)

theorem BlowUpLocRingInj.proof : BlowUpLocRingInj.Statement.{u} := by
  intro R _ K _ ι J P _ u Q Q' hQ hQh hQr hQle hQ' hQ'h hQ'r hQ'le heq
  exact le_antisymm (le_of_blowUpLocRing_le hQ hQh hQr hQle hQ'le heq.ge)
    (le_of_blowUpLocRing_le hQ' hQ'h hQ'r hQ'le hQle heq.le)

end BlowUpLocRingInj

end

end GroundTheory.Heights₂.Heights.NumbersDVR
