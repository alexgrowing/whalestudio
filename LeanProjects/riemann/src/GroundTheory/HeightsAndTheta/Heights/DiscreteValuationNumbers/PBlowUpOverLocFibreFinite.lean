import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFamilyFiniteCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingIso
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocInChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace BlowUpOverLocFibreFinite

theorem isAlgebraic_div {A L : Type*} [CommRing A] [Field L] [Algebra A L] (a b : A)
    (hb : algebraMap A L b ≠ 0) : IsAlgebraic A (algebraMap A L a / algebraMap A L b) := by
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => Polynomial.coeff p 1) h
    simp at h1
    rw [h1, map_zero]
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [mul_div_cancel₀ _ hb, sub_self]

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type u} [CommRing R]

def blowUpFrac (P : Ideal (MRing ι R)) (u : J → MRing ι R) :
    MRing (extIdx ι J) R →+* FractionRing (MRing ι R ⧸ P) :=
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).comp (blowUpEval P u)

theorem blowUpFrac_apply (P : Ideal (MRing ι R)) (u : J → MRing ι R) (F : MRing (extIdx ι J) R) :
    blowUpFrac P u F = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) := rfl

theorem blowUpFrac_X_none (P : Ideal (MRing ι R)) (u : J → MRing ι R) (j : J) :
    blowUpFrac P u (X ⟨none, j⟩) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u j)) := by
  rw [blowUpFrac_apply]
  congr 1
  show Polynomial.eval 1 (aeval (blowUpSubst P u) (newVar j : MRing (extIdx ι J) R)) = _
  rw [aeval_blowUpSubst_newVar]
  simp

theorem blowUpFrac_X_some (P : Ideal (MRing ι R)) (u : J → MRing ι R) (k : K) (i : ι k) :
    blowUpFrac P u (X ⟨some k, i⟩) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, i⟩)) := by
  rw [blowUpFrac_apply, ← blowUpEval_liftForm (J := J) P u, liftForm_X]

theorem blowUpFrac_C (P : Ideal (MRing ι R)) (u : J → MRing ι R) (r : R) :
    blowUpFrac P u (C r) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (C r)) := by
  rw [blowUpFrac_apply, ← blowUpEval_liftForm (J := J) P u, liftForm_C]

theorem blowUpLocRing_isLocal (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R)
    (Q : Ideal (MRing (extIdx ι J) R)) (hQ : Q.IsPrime) (hle : blowUpOf P u ≤ Q) :
    IsLocalRing (blowUpLocRing P u Q) ∧
      ∀ (z : blowUpLocRing P u Q) (b : Option K → ℕ) (F G : MRing (extIdx ι J) R), IsMultiHomog F b →
        IsMultiHomog G b → G ∉ Q →
        (z : FractionRing (MRing ι R ⧸ P)) =
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G) →
        (IsUnit z ↔ F ∉ Q) := by
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof R K ι J P u Q hle
  obtain ⟨-, hunit⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof R (Option K) (extIdx ι J)
    (blowUpOf P u) Q hQ hle
  have := (HomLocRingIsLocal.proof HomLocRingMem.proof R (Option K) (extIdx ι J)
    (blowUpOf P u) Q hQ hle).1
  refine ⟨φ.isLocalRing, fun z b F G hF hG hGQ hz => ?_⟩
  have e : z = φ ⟨_, Subring.subset_closure ⟨b, F, G, hF, hG, hGQ, rfl⟩⟩ :=
    (Subtype.ext ((hφ b F G hF hG hGQ).trans hz.symm)).symm
  rw [e]
  exact (MulEquiv.isUnit_map φ.toMulEquiv).trans (hunit b F G hF hG hGQ _)

theorem isMultiHomog_prod_X_pow (e : ∀ o, extIdx ι J o) (b : Option K → ℕ) :
    IsMultiHomog (∏ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o) b := by
  have h := IsWeightedHomogeneous.prod Finset.univ (fun o => (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o)
    (fun o => b o • blockWeight (extIdx ι J) ⟨o, e o⟩)
    (fun o _ => (isWeightedHomogeneous_X R (blockWeight (extIdx ι J)) ⟨o, e o⟩).pow (b o))
  have hb : (∑ o, b o • blockWeight (extIdx ι J) ⟨o, e o⟩) = b := by
    funext o'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hb] at h
  exact h

theorem prod_X_pow_not_mem {Q : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime)
    {e : ∀ o, extIdx ι J o} (he : ∀ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ∉ Q) (b : Option K → ℕ) :
    (∏ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o) ∉ Q := by
  haveI := hQ
  exact fun h => (Q.primeCompl.prod_mem fun o _ => Q.primeCompl.pow_mem (he o) _) h

def chartCoord (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (e : ∀ o, extIdx ι J o) :
    (Σ o, extIdx ι J o) → FractionRing (MRing ι R ⧸ P) :=
  fun v => blowUpFrac P u (X v) * (blowUpFrac P u (X ⟨v.1, e v.1⟩))⁻¹

def chartVal (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (e : ∀ o, extIdx ι J o) (F : MRing (extIdx ι J) R) :
    FractionRing (MRing ι R ⧸ P) :=
  eval₂ ((blowUpFrac P u).comp C) (chartCoord P u e) F

theorem chartVal_of_homog (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (e : ∀ o, extIdx ι J o)
    {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b) :
    chartVal P u e F = blowUpFrac P u F / blowUpFrac P u (∏ o, X ⟨o, e o⟩ ^ b o) := by
  have hφ : blowUpFrac P u = eval₂Hom ((blowUpFrac P u).comp C) (fun v => blowUpFrac P u (X v)) :=
    ringHom_ext (fun r => by simp) (fun v => by simp)
  refine (BlowUpOverLocInChart.eval₂_mul_fst_of_homog ((blowUpFrac P u).comp C) (fun v => blowUpFrac P u (X v))
    (fun o => (blowUpFrac P u (X ⟨o, e o⟩))⁻¹) hF).trans ?_
  have h1 : eval₂ ((blowUpFrac P u).comp C) (fun v => blowUpFrac P u (X v)) F = blowUpFrac P u F := by
    conv_rhs => rw [hφ]
    rfl
  rw [h1, map_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  simp only [map_pow, inv_pow]

variable [∀ k, Fintype (ι k)] [Fintype J]

set_option maxHeartbeats 1000000 in

theorem eq_of_le_of_mem_fibre (P W : Ideal (MRing ι R)) [P.IsPrime]
    (hN : IsNoetherianRing (homLocRing P W)) (hD : ringKrullDim (homLocRing P W) = 1)
    (hWp : W.IsPrime) (hPW : P ≤ W) (hWrel : IsRelevant W) (N : K → ℕ) (u : J → MRing ι R)
    (hu : ∀ j, IsMultiHomog (u j) N) (c : K → ℕ) (x : MRing ι R) (hx : IsMultiHomog x c) (hxP : x ∉ P)
    (hxW : x ∈ W) {Q₀ Q : Ideal (MRing (extIdx ι J) R)}
    (hQ₀ : Q₀.IsPrime ∧ IsMultiHomogIdeal Q₀ ∧ IsRelevant Q₀ ∧ blowUpOf P u ≤ Q₀ ∧
      Q₀.comap (liftForm (ι := ι) (J := J) (R := R)) = W)
    (hQ : Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧ blowUpOf P u ≤ Q ∧
      Q.comap (liftForm (ι := ι) (J := J) (R := R)) = W)
    (hle : Q₀ ≤ Q) : Q₀ = Q := by
  obtain ⟨hQ₀p, hQ₀h, hQ₀r, hQ₀le, hQ₀W⟩ := hQ₀
  obtain ⟨hQp, hQh, hQr, hQle, hQW⟩ := hQ
  haveI := hN
  by_contra hne
  choose e he using hQr
  have hL : ∀ f : MRing ι R, f ∉ P →
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) ≠ 0 :=
    fun f hf => HomLocRingMem.algebraMap_mk_ne_zero P hf

  have hφne : ∀ {F : MRing (extIdx ι J) R} {b : Option K → ℕ}, IsMultiHomog F b → F ∉ blowUpOf P u →
      blowUpFrac P u F ≠ 0 := by
    intro F b hF hFn h0
    apply hFn
    rw [blowUpFrac_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h0
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_of_isMultiHomog P u hF, h0, map_zero, zero_mul]
  have hG : ∀ b : Option K → ℕ, IsMultiHomog (∏ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o) b :=
    fun b => isMultiHomog_prod_X_pow e b
  have hGQ : ∀ b : Option K → ℕ, (∏ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o) ∉ Q := prod_X_pow_not_mem hQp he
  have hφe : ∀ o, blowUpFrac P u (X ⟨o, e o⟩) ≠ 0 := fun o =>
    hφne (isWeightedHomogeneous_X R (blockWeight (extIdx ι J)) ⟨o, e o⟩) fun h => he o (hQle h)

  let B : Subalgebra (homLocRing P W) (FractionRing (MRing ι R ⧸ P)) :=
    Algebra.adjoin (homLocRing P W) (Set.range (chartCoord P u e))
  have hCA : ∀ r : R, blowUpFrac P u (C r) ∈ homLocRing P W := by
    intro r
    refine Subring.subset_closure ⟨0, C r, 1, isWeightedHomogeneous_C _ r, isWeightedHomogeneous_one R _,
      fun h => hWp.ne_top ((Ideal.eq_top_iff_one W).mpr h), ?_⟩
    rw [map_one, map_one, div_one, blowUpFrac_C]
  have hτB : ∀ F, chartVal P u e F ∈ B := by
    intro F
    refine MvPolynomial.induction_on (motive := fun F => chartVal P u e F ∈ B) F (fun r => ?_) (fun p q hp hq => ?_) (fun p v hp => ?_)
    · show eval₂ _ _ (C r) ∈ B
      rw [eval₂_C]
      exact Subalgebra.algebraMap_mem B (⟨_, hCA r⟩ : homLocRing P W)
    · show eval₂ _ _ (p + q) ∈ B
      rw [eval₂_add]
      exact add_mem hp hq
    · show eval₂ _ _ (p * X v) ∈ B
      rw [eval₂_mul, eval₂_X]
      exact mul_mem hp (Algebra.subset_adjoin ⟨v, rfl⟩)

  have hτD : ∀ {Q' : Ideal (MRing (extIdx ι J) R)}, Q' ≤ Q → ∀ {F : MRing (extIdx ι J) R} {b : Option K → ℕ},
      IsMultiHomog F b → chartVal P u e F ∈ blowUpLocRing P u Q' := fun hQ' F b hF =>
    Subring.subset_closure ⟨b, F, _, hF, hG b, fun h => hGQ b (hQ' h), chartVal_of_homog P u e hF⟩
  have hBD : ∀ {Q' : Ideal (MRing (extIdx ι J) R)}, Q'.IsPrime → IsMultiHomogIdeal Q' → IsRelevant Q' →
      blowUpOf P u ≤ Q' → Q'.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ W → Q' ≤ Q →
      ∀ z ∈ B, z ∈ blowUpLocRing P u Q' := by
    intro Q' h1 h2 h3 h4 h5 h6 z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      have h := hτD h6 (isWeightedHomogeneous_X R (blockWeight (extIdx ι J)) v)
      rwa [chartVal, eval₂_X] at h
    | algebraMap r =>
      have h := homLocRing_le_blowUpOverLoc P W u r.2
      simp only [blowUpOverLoc, Subring.mem_iInf] at h
      exact h Q' ⟨h1, h2, h3, h4, h5⟩
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hBQ := hBD hQp hQh (fun o => ⟨e o, he o⟩) hQle hQW.le le_rfl
  have hBQ₀ := hBD hQ₀p hQ₀h hQ₀r hQ₀le hQ₀W.le hle

  obtain ⟨hloc, hunit⟩ := blowUpLocRing_isLocal P u Q hQp hQle
  obtain ⟨hloc₀, hunit₀⟩ := blowUpLocRing_isLocal P u Q₀ hQ₀p hQ₀le
  let f : B →+* blowUpLocRing P u Q :=
    ((B.val : B →ₐ[homLocRing P W] FractionRing (MRing ι R ⧸ P)) : B →+* _).codRestrict _ fun z => hBQ z z.2
  let f₀ : B →+* blowUpLocRing P u Q₀ :=
    ((B.val : B →ₐ[homLocRing P W] FractionRing (MRing ι R ⧸ P)) : B →+* _).codRestrict _ fun z => hBQ₀ z z.2
  let 𝔮 : Ideal B := (IsLocalRing.maximalIdeal _).comap f
  let 𝔮₀ : Ideal B := (IsLocalRing.maximalIdeal _).comap f₀
  have hmem : ∀ z, z ∈ 𝔮 ↔ ¬ IsUnit (f z) := fun z => by
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hmem₀ : ∀ z, z ∈ 𝔮₀ ↔ ¬ IsUnit (f₀ z) := fun z => by
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hform : ∀ {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b),
      ((⟨_, hτB F⟩ : B) ∈ 𝔮 ↔ F ∈ Q) := fun {F} {b} hF => by
    rw [hmem, hunit _ b F _ hF (hG b) (hGQ b) (chartVal_of_homog P u e hF), not_not]
  have hform₀ : ∀ {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b),
      ((⟨_, hτB F⟩ : B) ∈ 𝔮₀ ↔ F ∈ Q₀) := fun {F} {b} hF => by
    rw [hmem₀, hunit₀ _ b F _ hF (hG b) (fun h => hGQ b (hle h)) (chartVal_of_homog P u e hF), not_not]
  have hDD : blowUpLocRing P u Q ≤ blowUpLocRing P u Q₀ :=
    Subring.closure_mono fun z ⟨b, F, G', hF, hG', hG'Q, hz⟩ => ⟨b, F, G', hF, hG', fun h => hG'Q (hle h), hz⟩
  have hmono : 𝔮₀ ≤ 𝔮 := by
    intro z hz
    rw [hmem₀] at hz
    rw [hmem]
    intro hu
    exact hz (hu.map (Subring.inclusion hDD))

  have hx₀ : (⟨_, hτB (liftForm x)⟩ : B) ∈ 𝔮₀ := (hform₀ (isMultiHomog_liftForm hx)).mpr (by
    rw [← Ideal.mem_comap, hQ₀W]
    exact hxW)
  have h0 : (⊥ : Ideal B) < 𝔮₀ := by
    refine bot_lt_iff_ne_bot.mpr fun hb => ?_
    rw [hb, Ideal.mem_bot] at hx₀
    have h := congrArg Subtype.val hx₀
    rw [show ((⟨_, hτB (liftForm x)⟩ : B) : FractionRing (MRing ι R ⧸ P)) = chartVal P u e (liftForm x) from rfl,
      chartVal_of_homog P u e (isMultiHomog_liftForm hx), blowUpFrac_apply, blowUpEval_liftForm] at h
    exact div_ne_zero (hL x hxP) (hφne (hG _) fun h' => hGQ _ (hQle h')) h

  obtain ⟨F, hFQ, hFQ₀⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  obtain ⟨b, hbQ₀⟩ : ∃ b, weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F ∉ Q₀ := by
    by_contra h
    push_neg at h
    apply hFQ₀
    rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) F]
    exact finsum_induction (· ∈ Q₀) (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) h
  have hFb := weightedHomogeneousComponent_isWeightedHomogeneous (R := R) (w := blockWeight (extIdx ι J)) b F
  have h01 : 𝔮₀ < 𝔮 := by
    refine lt_of_le_of_ne hmono fun h => hbQ₀ ((hform₀ hFb).mp ?_)
    rw [h]
    exact (hform hFb).mpr (hQh F hFQ b)

  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h01
  rw [Ideal.height_bot] at e1
  have h2 : (2 : ℕ∞) ≤ 𝔮.height :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ 𝔮₀.height + 1 := add_le_add e1 le_rfl
      _ ≤ 𝔮.height := e2
  haveI : Algebra.FiniteType (homLocRing P W) B :=
    Algebra.FiniteType.adjoin_of_finite (R := homLocRing P W) (t := Set.range (chartCoord P u e)) (Set.finite_range _)
  haveI hAlg : Algebra.IsAlgebraic (homLocRing P W) B := by
    refine (Subalgebra.isAlgebraic_iff B).mp (Algebra.isAlgebraic_adjoin_iff.mpr ?_)
    rintro _ ⟨⟨o, i⟩, rfl⟩
    cases o with
    | none =>
      obtain ⟨i₀, hi₀⟩ := powMonomial_not_mem hWp hWrel N
      have hmP : powMonomial N i₀ ∉ P := fun h => hi₀ (hPW h)
      have ha : ∀ k : J, algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u k)) /
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i₀)) ∈
            homLocRing P W := fun k =>
        Subring.subset_closure ⟨N, u k, powMonomial N i₀, hu k, isMultiHomog_powMonomial N i₀, hi₀, rfl⟩
      have hj : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u (e none))) ≠ 0 :=
        fun h => hφe none (by rw [← h]; exact blowUpFrac_X_none P u (e none))
      have key : chartCoord P u e ⟨none, i⟩ =
          (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u i)) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i₀))) /
          (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u (e none))) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i₀))) := by
        show blowUpFrac P u (X ⟨none, i⟩) * (blowUpFrac P u (X ⟨none, e none⟩))⁻¹ = _ / _
        rw [show blowUpFrac P u (X ⟨none, i⟩) = _ from blowUpFrac_X_none P u i,
          show blowUpFrac P u (X ⟨none, e none⟩) = _ from blowUpFrac_X_none P u (e none),
          div_div_div_cancel_right₀ (hL _ hmP), div_eq_mul_inv]
      rw [key]
      exact isAlgebraic_div (⟨_, ha i⟩ : homLocRing P W) ⟨_, ha (e none)⟩ (div_ne_zero hj (hL _ hmP))
    | some k =>
      have hnot : (X ⟨k, e (some k)⟩ : MRing ι R) ∉ W := fun h => he (some k) (by
        rw [← hQW, Ideal.mem_comap, liftForm_X] at h
        exact h)
      have hmemA : chartCoord P u e ⟨some k, i⟩ ∈ homLocRing P W := by
        refine Subring.subset_closure ⟨Pi.single k 1, X ⟨k, i⟩, X ⟨k, e (some k)⟩,
          isWeightedHomogeneous_X R (blockWeight ι) ⟨k, i⟩,
          isWeightedHomogeneous_X R (blockWeight ι) ⟨k, e (some k)⟩, hnot, ?_⟩
        show blowUpFrac P u (X ⟨some k, i⟩) * (blowUpFrac P u (X ⟨some k, e (some k)⟩))⁻¹ = _
        rw [show blowUpFrac P u (X ⟨some k, i⟩) = _ from blowUpFrac_X_some P u k i,
          show blowUpFrac P u (X ⟨some k, e (some k)⟩) = _ from blowUpFrac_X_some P u k (e (some k)),
          div_eq_mul_inv]
      exact isAlgebraic_algebraMap (⟨_, hmemA⟩ : homLocRing P W)
  have hinj : Function.Injective (algebraMap (homLocRing P W) B) := fun a a' h => by
    have h' := congrArg (fun z : B => (z : FractionRing (MRing ι R ⧸ P))) h
    exact Subtype.ext h'
  have hdi := DimensionInequality.full (homLocRing P W) B hinj 𝔮
  rw [trdeg_eq_zero (R := homLocRing P W) (A := B), add_zero] at hdi
  have h3 : 𝔮.height ≤ (𝔮.under (homLocRing P W)).height :=
    Cardinal.ofENat_le_ofENat.mp (le_trans le_self_add hdi)
  have h4 : (𝔮.under (homLocRing P W)).height ≤ 1 := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔮.under (homLocRing P W))
    rw [hD] at h
    exact_mod_cast h
  have h5 := h2.trans (h3.trans h4)
  norm_num at h5

end BlowUpOverLocFibreFinite

open BlowUpOverLocFibreFinite in

theorem BlowUpOverLocFibreFinite.proof : BlowUpOverLocFibreFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have hPp : P.IsPrime := hP.multiProj.isPrime
  obtain ⟨-, hNoeth, hDim⟩ := HomLocRingLocal.proof (HomLocRingIsLocal.proof HomLocRingMem.proof)
    (HomLocRingNoetherian.proof HomLocRingMem.proof)
    (HomLocRingDimLe.proof HomLocRingMem.proof (HomLocRingIsLocal.proof HomLocRingMem.proof))
    O K ι P hP.multiProj c x hx hxP W hWmin hWrel
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hI : IsMultiHomogIdeal (blowUpOf P u ⊔ Ideal.span {liftForm (J := J) x}) :=
    SupSpanMultiHomog.proof O (Option K) (extIdx ι J) (blowUpOf P u) (liftForm x) (liftMDeg c)
      (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
    (blowUpOf P u ⊔ Ideal.span {liftForm (J := J) x})).subset ?_
  rintro Q ⟨hQp, hQh, hQr, hQle, hQW⟩
  have hxQ : liftForm x ∈ Q := by
    rw [← Ideal.mem_comap, hQW]
    exact hxW
  refine ⟨⟨hQp, sup_le hQle ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩, fun Q' hQ' hQ'Q => ?_⟩
  haveI := hQ'.1
  obtain ⟨Q₀, hQ₀, hQ₀Q'⟩ := Ideal.exists_minimalPrimes_le hQ'.2
  have hQ₀p : Q₀.IsPrime := hQ₀.1.1
  have hQ₀Q : Q₀ ≤ Q := hQ₀Q'.trans hQ'Q
  have hQ₀h := MinimalPrimeMultiHomog.proof O (Option K) (extIdx ι J) _ Q₀ hI hQ₀
  have hQ₀r : IsRelevant Q₀ := fun o =>
    let ⟨i, hi⟩ := hQr o
    ⟨i, fun h => hi (hQ₀Q h)⟩
  have hQ₀le : blowUpOf P u ≤ Q₀ := le_sup_left.trans hQ₀.1.2
  have hQ₀W : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) = W := by
    have hle : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := hQW ▸ Ideal.comap_mono hQ₀Q
    refine le_antisymm hle (hWmin.2 ⟨Ideal.comap_isPrime _ _,
      sup_le (fun p hp => hQ₀le (liftForm_mem_blowUpOf hp)) ?_⟩ hle)
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact hQ₀.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have h := eq_of_le_of_mem_fibre P W hNoeth hDim hWp hPW hWrel N u hu c x hx hxP hxW
    ⟨hQ₀p, hQ₀h, hQ₀r, hQ₀le, hQ₀W⟩ ⟨hQp, hQh, hQr, hQle, hQW⟩ hQ₀Q
  exact h ▸ hQ₀Q'

end

end GroundTheory.Heights₂.Heights.NumbersDVR
