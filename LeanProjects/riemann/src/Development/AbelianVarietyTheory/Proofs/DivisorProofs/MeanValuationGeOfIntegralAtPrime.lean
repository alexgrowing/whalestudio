import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation

open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.FunObj.SqNum.MeanValLow

variable {K : Type} [Field K] [NumberField K]

theorem vw_eq_zero_of_notMem (w : Formalism.PairingDivisionLocalBalance.Pl K) {a : 𝓞 K} (ha : a ∉ w.asIdeal) : Formalism.DivisionValues.vw w (a : K) = 0 := by
  classical
  have ha0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rintro rfl
    exact ha w.asIdeal.zero_mem
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ ha0]
  by_contra h
  have h' : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
    intro h0
    exact h (by rw [h0]; rfl)
  exact ha (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd ha0 w.irreducible).1 h'))

theorem vw_int_nonneg (w : Formalism.PairingDivisionLocalBalance.Pl K) (a : 𝓞 K) : 0 ≤ Formalism.DivisionValues.vw w (a : K) := by
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_mul (w : Formalism.PairingDivisionLocalBalance.Pl K) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b := by
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul K w ((FractionalIdeal.spanSingleton_ne_zero_iff).2 ha)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hb)

theorem vw_pow (w : Formalism.PairingDivisionLocalBalance.Pl K) (a : K) (n : ℕ) : Formalism.DivisionValues.vw w (a ^ n) = n * Formalism.DivisionValues.vw w a := by
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

theorem coeff_zero_mem (σ : K →+* ℂ) {δ : ℂ} (hδ : IsIntegral ℤ δ) {q : K[X]} (hq : IsMinPol σ δ q) :
    ∃ b : 𝓞 K, (b : K) = q.coeff 0 := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Algebra (𝓞 K) ℂ := ((algebraMap K ℂ).comp (algebraMap (𝓞 K) K)).toAlgebra
  haveI : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℤ (𝓞 K) ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hi : IsIntegral (𝓞 K) δ := hδ.tower_top
  have e := minpoly.isIntegrallyClosed_eq_field_fractions' K hi
  refine ⟨(minpoly (𝓞 K) δ).coeff 0, ?_⟩
  rw [hq.eq_minpoly, e, coeff_map]

end GlobalTheory.FunObj.SqNum.MeanValLow

open GlobalTheory.FunObj.SqNum.MeanValLow in

theorem GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}, GlobalTheory.FunObj.SqNum.IsMinPol σ β p → β ≠ 0 → ∀ {c : K}, c ≠ 0 → ∀ {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl K}, (l : 𝓞 K) ∈ w.asIdeal → ∀ {m : ℕ}, GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ m * (σ c * β)) → -((m : ℝ) * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w c : ℝ) + GlobalTheory.FunObj.SqNum.meanVal_vw w p := by
  intro K _ _ σ β p hp hβ c hc l hl w hw m ⟨n, hn, hint⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hn
    exact hl.one_lt.ne' hn
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn0
  have hlm : (l : K) ^ m ≠ 0 := pow_ne_zero _ hl0
  set a : K := (n : K) * (l : K) ^ m * c with ha_def
  have ha : a ≠ 0 := mul_ne_zero (mul_ne_zero hnK hlm) hc
  have hδ : IsIntegral ℤ (σ a * β) := by
    have e : σ a * β = (n : ℂ) * ((l : ℂ) ^ m * (σ c * β)) := by
      simp only [a, map_mul, map_pow, map_natCast]; ring
    rw [e]; exact hint
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsScalarTower ℤ K ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hK : IsIntegral K (σ a * β) := hδ.tower_top
  have hq : IsMinPol σ (σ a * β) (minpoly K (σ a * β)) :=
    ⟨minpoly.monic hK, minpoly.irreducible hK, minpoly.aeval K (σ a * β)⟩
  obtain ⟨b, hb⟩ := coeff_zero_mem σ hδ hq
  have eq := hp.scaleRoots_eq hq ha
  obtain ⟨hc0, hd⟩ := hp.ne_zero hβ
  rw [eq, coeff_scaleRoots, Nat.sub_zero] at hb
  have h0 : 0 ≤ Formalism.DivisionValues.vw w (p.coeff 0 * a ^ p.natDegree) := hb ▸ vw_int_nonneg w b
  rw [vw_mul w hc0 (pow_ne_zero _ ha), vw_pow, ha_def, vw_mul w (mul_ne_zero hnK hlm) hc,
    vw_mul w hnK hlm, vw_pow] at h0
  have hnw : (n : 𝓞 K) ∉ w.asIdeal := by
    intro hn'
    obtain ⟨x, y, e'⟩ := (Nat.isCoprime_iff_coprime.2 hn).map (Int.castRingHom (𝓞 K))
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e']
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hn')) (Ideal.mul_mem_left _ _ (by simpa using hw))
  have hvn : Formalism.DivisionValues.vw w (n : K) = 0 := by
    have := vw_eq_zero_of_notMem w hnw
    simpa using this
  rw [hvn] at h0
  have hdpos : (0 : ℝ) < p.natDegree := by exact_mod_cast Nat.pos_of_ne_zero hd
  unfold GlobalTheory.FunObj.SqNum.meanVal_vw
  have h1 : (0 : ℝ) ≤ (Formalism.DivisionValues.vw w (p.coeff 0) : ℝ) + p.natDegree * ((m : ℝ) * Formalism.DivisionValues.vw w (l : K) + Formalism.DivisionValues.vw w c) := by
    have := (Int.cast_le (R := ℝ)).2 h0
    push_cast at this
    linarith
  have h2 : -((m : ℝ) * Formalism.DivisionValues.vw w (l : K) + Formalism.DivisionValues.vw w c) ≤ (Formalism.DivisionValues.vw w (p.coeff 0) : ℝ) / p.natDegree := by
    rw [le_div_iff₀ hdpos]; linarith
  linarith
