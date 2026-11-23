import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.CMPrimeIdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace EulerTie

variable (F E) in

def finComp : AE F E →+* FiniteAdeleRing (𝓞 E) E := (toFinAd F E).comp (finPart F E)

omit [NumberField E] in
theorem parts_extZero (y : Af F ⊗[F] E) :
    infPart F E (extZero F E y) = 0 ∧ finPart F E (extZero F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, and_self]
  | tmul a x => exact ⟨TensorProduct.zero_tmul _ _, rfl⟩
  | add a b ha hb => simp only [map_add, ha.1, ha.2, hb.1, hb.2, add_zero, and_self]

theorem comp_finComp : Comp (finComp F E) := by
  let c := (Algebra.TensorProduct.comm F E (Af F)).toRingEquiv
  have hι : ∀ x a, ((toFinAd F E).comp c.toRingHom) (x ⊗ₜ[F] a) =
      algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)
  have hs : ∀ y, ((toFinAd F E).comp c.toRingHom) (swapAf F E y) = toFinAd F E y := fun y =>
    congrArg (toFinAd F E) ((Algebra.TensorProduct.comm F (Af F) E).symm_apply_apply y)
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨fun z h1 h2 => ?_, fun s => ?_, fun x => ?_, fun z => ?_, fun a Q => ?_⟩
  · have h3 : finPart F E z = 0 := toFinAd_bijective.1 (h2.trans (map_zero _).symm)
    apply e.injective
    rw [map_zero]
    exact Prod.ext ((he z).1.trans h1) ((he z).2.trans h3)
  · obtain ⟨y, rfl⟩ := (toFinAd_bijective (F := F)).2 s
    exact ⟨_, (parts_extZero y).1, congrArg (toFinAd F E) (parts_extZero y).2⟩
  · change toFinAd F E ((1 : Af F) ⊗ₜ[F] x) = _
    rw [toFinAd_tmul, map_one, one_mul]
  · rw [mem_intAE_iff]
    refine ⟨fun h => ?_, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_⟩
    · have := GlobalTheory.AdeleBaseChange.map_mem_int hι h
      rw [hs] at this
      exact this
    · rw [hs]; exact h
  · change toFinAd F E (a.2 ⊗ₜ[F] (1 : E)) Q = _
    rw [toFinAd_tmul, map_one, mul_one]
    rfl

theorem parts_locIdele (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    infPart F E (locIdele F P u : AE F E) = 1 ∧
      finComp F E (locIdele F P u : AE F E) = (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 E) E) := by
  have e : (locIdele F P u : AE F E) = 1 - extZero F E 1 +
      extZero F E ((finAdEquiv F E).symm (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 E) E)) := rfl
  rw [e]
  constructor
  · rw [RingHom.map_add, RingHom.map_sub, RingHom.map_one, (parts_extZero _).1, (parts_extZero _).1, sub_zero, add_zero]
  · change toFinAd F E (finPart F E _) = _
    rw [RingHom.map_add, RingHom.map_sub, RingHom.map_one, (parts_extZero _).2, (parts_extZero _).2, sub_self, zero_add]
    exact (finAdEquiv F E).apply_symm_apply _

theorem comp_glue {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (he : IsDelta (finComp F E) P e) (a : AE F E) :
    infPart F E (e * a + (1 - e)) = 1 ∧ finComp F E (e * a + (1 - e)) P = finComp F E a P ∧
      ∀ Q, Q ≠ P → finComp F E (e * a + (1 - e)) Q = 1 := by
  have h : ∀ Q, finComp F E (e * a + (1 - e)) Q = finComp F E e Q * finComp F E a Q + (1 - finComp F E e Q) :=
    fun Q => by rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]; rfl
  refine ⟨?_, ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, he.1, zero_mul, sub_zero, zero_add]
  · rw [h, he.2.1, one_mul, sub_self, add_zero]
  · rw [h, he.2.2 Q hQ, zero_mul, sub_zero, zero_add]

theorem finComp_locIdele_self (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    finComp F E (locIdele F P u : AE F E) P = u := by
  rw [(parts_locIdele P u).2, GlobalTheory.CMVal.single_self]

theorem finComp_locIdele_ne {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ P) (u : (P.adicCompletion E)ˣ) :
    finComp F E (locIdele F P u : AE F E) Q = 1 := by
  classical
  rw [(parts_locIdele P u).2, GlobalTheory.CMVal.single_apply]
  exact Function.update_of_ne h _ _

theorem glue_eq_locIdele {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (he : IsDelta (finComp F E) P e) {a : AE F E}
    {u : (P.adicCompletion E)ˣ} (h : finComp F E a P = u) : e * a + (1 - e) = (locIdele F P u : AE F E) := by
  obtain ⟨h1, h2, h3⟩ := comp_glue he a
  refine comp_finComp.ext' (h1.trans (parts_locIdele P u).1.symm) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [h2, h, finComp_locIdele_self]
  · rw [h3 Q hQ, finComp_locIdele_ne hQ]

theorem locIdele_int_iff (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    finPart F E (locIdele F P u : AE F E) ∈ intAE F E ↔ Valued.v (u : P.adicCompletion E) ≤ 1 := by
  rw [comp_finComp.2.2.2.1]
  refine ⟨fun h => ?_, fun h Q => ?_⟩
  · have := h P
    rwa [finComp_locIdele_self] at this
  · by_cases hQ : Q = P
    · subst hQ; rw [finComp_locIdele_self]; exact h
    · rw [finComp_locIdele_ne hQ]; exact one_mem _

theorem isUnitAt_iff (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Formalism.L2.Host.IsUnitAt P u ↔ Valued.v (u : P.adicCompletion E) ≤ 1 ∧
      Valued.v ((u⁻¹ : (P.adicCompletion E)ˣ) : P.adicCompletion E) ≤ 1 := by
  have h0 : 0 < Valued.v (u : P.adicCompletion E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 u.ne_zero)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ h0]
  exact le_antisymm_iff

variable {σ : E →ₐ[F] E}

theorem isDelta_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E} (h : IsPrimeIdem σ P e f) :
    IsDelta (finComp F E) P e := by
  rcases h with ⟨⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩, -⟩ | ⟨-, ⟨v, ε, hε, h3⟩, ht⟩
  · refine (tie_iff comp_finComp h1 ?_ P).1 ht
    have : e = e * algebraMap (AF F) (AE F E) ε := by rw [← h3, mul_add, h1, h2, add_zero]
    rw [this, RingHom.map_mul, (place_comp (comp_finComp (E := E)) hε).1, mul_zero]
  · obtain ⟨k0, k1, k2⟩ := place_comp (comp_finComp (E := E)) hε
    rw [← h3] at k0 k1 k2
    refine (tie_iff comp_finComp (comp_finComp.ext' (by rw [RingHom.map_mul, k0, mul_zero]) fun Q => ?_) k0 P).1 ht
    rw [ev_mul]
    by_cases hQ : Q.under (𝓞 F) = v
    · rw [k1 Q hQ, mul_one]
    · rw [k2 Q hQ, mul_zero]

theorem valuation_of_mem_notMem_sq (P : HeightOneSpectrum (𝓞 E)) {a : 𝓞 E} (h1 : a ∈ P.asIdeal)
    (h2 : a ∉ P.asIdeal ^ 2) : P.valuation E (a : E) = WithZero.exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have k1 : P.intValuation a ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; simpa using h1
  have k2 : ¬ P.intValuation a ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact h2
  have h0 : P.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero P a ha
  refine (HeightOneSpectrum.valuation_of_algebraMap P a).trans ?_
  rw [← WithZero.exp_log h0] at k1 k2 ⊢
  rw [WithZero.exp_le_exp] at k1 k2
  congr 1
  omega

theorem exists_of_isUnifIdele {P : HeightOneSpectrum (𝓞 E)} {x : (AE F E)ˣ} (h : IsUnifIdele σ P x) :
    ∃ u, Formalism.L2.Host.IsUnifAt P u ∧ x = locIdele F P u := by
  obtain ⟨e, f, ϖ, he, h1, h2, hx⟩ := h
  have hv : Valued.v (algebraMap E (P.adicCompletion E) (ϖ : E)) = WithZero.exp (-1 : ℤ) :=
    (Formalism.UG.P.levelaf_valued_algebraMap _ _).trans (valuation_of_mem_notMem_sq P h1 h2)
  have h0 : algebraMap E (P.adicCompletion E) (ϖ : E) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  refine ⟨Units.mk0 _ h0, hv, Units.ext (hx.trans (glue_eq_locIdele (isDelta_of_isPrimeIdem he) ?_))⟩
  rw [comp_finComp.2.2.1]
  rfl

end EulerTie

open EulerTie

variable {σ : E →ₐ[F] E}

theorem isUnramAt_iff_unrAt (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) :
    IsUnramAt σ χ P ↔ UnrAt χ P := by
  constructor
  · rintro ⟨e, f, he, h⟩ u hu
    obtain ⟨h1, h2⟩ := (isUnitAt_iff P u).1 hu
    have := h (locIdele F P u) (glue_eq_locIdele (isDelta_of_isPrimeIdem he) (finComp_locIdele_self P u)).symm
      ((locIdele_int_iff P u).2 h1) (by rw [← map_inv]; exact (locIdele_int_iff P u⁻¹).2 h2)
    exact (congrArg Circle.toUnits this).trans (map_one _)
  · intro h
    obtain ⟨e, f, -, he⟩ := exists_isPrimeIdem hσ P
    refine ⟨e, f, he, fun x hx h1 h2 => ?_⟩
    let π : AE F E →+* P.adicCompletion E := (evalV E P).toRingHom.comp (finComp F E)
    obtain ⟨u, rfl⟩ : ∃ u, x = locIdele F P u :=
      ⟨Units.map π.toMonoidHom x, Units.ext (hx.trans (glue_eq_locIdele (isDelta_of_isPrimeIdem he) rfl))⟩
    rw [← map_inv] at h2
    have := h u ((isUnitAt_iff P u).2 ⟨(locIdele_int_iff P u).1 h1, (locIdele_int_iff P u⁻¹).1 h2⟩)
    exact Circle.ext (congrArg Units.val this)

theorem chiAt_eq_val (hσ : IsCMExt F E σ) {χ : (AE F E)ˣ →* Circle} {P : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ P) :
    chiAt σ χ P = (val χ P : ℂ) := by
  have hc : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x := ⟨(isUnramAt_iff_unrAt hσ χ P).2 h, exists_isUnifIdele hσ P⟩
  obtain ⟨u, hu, e⟩ := exists_of_isUnifIdele hc.2.choose_spec
  rw [chiAt, dif_pos hc, e, ← h.locChar_eq_val hu]
  rfl

theorem chiAt_eq_zero (hσ : IsCMExt F E σ) {χ : (AE F E)ˣ →* Circle} {P : HeightOneSpectrum (𝓞 E)}
    (h : ¬ UnrAt χ P) : chiAt σ χ P = 0 :=
  dif_neg fun hc => h ((isUnramAt_iff_unrAt hσ χ P).1 hc.1)

theorem lfac_eq_locL (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    lfac σ χ P s = locL (charFam χ) P s := by
  unfold lfac locL charFam
  split_ifs with h
  · rw [chiAt_eq_val hσ h, eulerFac_singleton]; rfl
  · rw [chiAt_eq_zero hσ h, eulerFac_zero, zero_mul, sub_zero, inv_one]

end GlobalTheory.LFun

end
