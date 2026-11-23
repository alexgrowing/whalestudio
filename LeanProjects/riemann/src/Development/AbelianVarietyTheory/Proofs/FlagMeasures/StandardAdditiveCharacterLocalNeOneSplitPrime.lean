import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne

noncomputable section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.PsiLoc

theorem not_dvd_different {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (h : SplitsIn E p)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P) : ¬ P ∣ differentIdeal ℤ (𝓞 E) := by
  intro hdvd
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).2 (Nat.prime_iff_prime_int.1 hp)).isMaximal
      (by simpa using hp0)
  have hlies : ∀ Q : Ideal (𝓞 E), Q.IsPrime → (p : 𝓞 E) ∈ Q →
      Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    intro Q hQ hpQ
    constructor
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hQ.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 E) (p : ℤ) ∈ Q
    simpa using hpQ
  haveI := hlies P hP hm
  have hnorm := Ideal.absNorm_eq_pow_inertiaDeg' P hp
  have hne1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P ≠ 0 := by
    intro h0; rw [h0, pow_zero] at hnorm; exact hne1 hnorm
  have h1 : p ∣ Ideal.absNorm P := by rw [hnorm]; exact dvd_pow_self p hf
  have h2 : Ideal.absNorm P ∣ (discr E).natAbs := by
    rw [← NumberField.absNorm_differentIdeal E (𝓞 E)]; exact map_dvd Ideal.absNorm hdvd
  have h3 : (p : ℤ) ∣ discr E := Int.natCast_dvd.2 (h1.trans h2)
  refine GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp E ?_ h3
  have hset : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) =
      (fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal) '' placesOver E p := by
    ext Q
    constructor
    · rintro ⟨hQ, hQl⟩
      have hpQ : (p : 𝓞 E) ∈ Q := by
        have : (p : ℤ) ∈ Q.under ℤ := hQl.over ▸ Ideal.mem_span_singleton_self _
        simpa [Ideal.under] using this
      have hQbot : Q ≠ ⊥ := by
        rintro rfl
        rw [Ideal.mem_bot] at hpQ
        exact hp.ne_zero (by exact_mod_cast hpQ)
      exact ⟨⟨Q, hQ, hQbot⟩, hpQ, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.isPrime, hlies _ w.isPrime hw⟩
  unfold SplitsIn at h
  rw [hset, Set.ncard_image_of_injective _ (fun a b hab => HeightOneSpectrum.ext hab), h]

theorem exists_eq_mul {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (h : SplitsIn E p)
    (x : 𝓞 E) (hx : ∀ y : 𝓞 E, ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ E ((p : E)⁻¹ * x * y)) :
    ∃ z : 𝓞 E, (x : E) = p * z := by
  have hp0 : (p : E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcop : differentIdeal ℤ (𝓞 E) ⊔ Ideal.span {(p : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpP : (p : 𝓞 E) ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    exact not_dvd_different hp h P hpP (Ideal.dvd_iff_le.2 (le_trans le_sup_left hle))
  have hdual : (p : E)⁻¹ * x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _)]
    intro a ha
    obtain ⟨y, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨n, hn⟩ := hx y
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, hn]
  have hmul : ∀ d ∈ differentIdeal ℤ (𝓞 E), ∃ b : 𝓞 E, (d : E) * ((p : E)⁻¹ * x) = b := by
    intro d hd
    have h1 : (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
    rw [coeIdeal_differentIdeal ℤ ℚ] at h1
    have h2 := FractionalIdeal.mul_mem_mul h1 hdual
    rw [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _))] at h2
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h2
    exact ⟨b, hb.symm⟩
  have h1 : (1 : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) ⊔ Ideal.span {(p : 𝓞 E)} := hcop ▸ Submodule.mem_top
  obtain ⟨d, hd, q, hq, hdq⟩ := Submodule.mem_sup.1 h1
  obtain ⟨b, hb⟩ := hmul d hd
  have hdx : d * x = p * b := by
    apply RingOfIntegers.ext
    push_cast
    rw [show (p : E) * (b : E) = p * ((d : E) * ((p : E)⁻¹ * x)) by rw [hb]]
    field_simp
  have hxp : x ∈ Ideal.span {(p : 𝓞 E)} := by
    have : x = d * x + q * x := by rw [← add_mul, hdq, one_mul]
    rw [this, hdx]
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.mul_mem_right _ _ hq)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hxp
  exact ⟨z, by rw [← hz]; push_cast; ring⟩

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ie_mem (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] v.adicCompletion F} (ha : a ∈ intV E v) :
    Formalism.UG.P.afsplitIE v a ∈ OAd F E := by
  have hgen : ∀ y ∈ v.adicCompletionIntegers F,
      ((1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v y : E ⊗[F] Ad F) ∈ OAd F E := fun y hy =>
    Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd v y hy⟩, rfl⟩)
  induction ha using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨y, hy⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · rw [Formalism.UG.P.afsplitIE_tmul]
      have : (y ⊗ₜ[F] Formalism.UG.P.afsplitI v 1 : E ⊗[F] Ad F) =
          (y ⊗ₜ[F] (1 : Ad F)) * ((1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v 1) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨y, hy⟩, rfl⟩)) (hgen 1 (one_mem _))
    · rw [Formalism.UG.P.afsplitIE_tmul]
      exact hgen y hy
  | zero => rw [map_zero]; exact zero_mem _
  | one =>
    rw [Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul]
    exact hgen 1 (one_mem _)
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem ie_mul_prV (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] v.adicCompletion F) (y : E ⊗[F] Ad F) :
    Formalism.UG.P.afsplitIE v (a * prV (E := E) v y) = Formalism.UG.P.afsplitIE v a * y := by
  rw [map_mul, Formalism.UG.P.afsplit_decomp, ← mul_assoc, mul_comm (Formalism.UG.P.afsplitIE v a),
    Formalism.UG.P.afsplit_eps_mul_IE]

theorem exists_inv (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ} (hpq : p.Coprime q) (hv : (p : 𝓞 F) ∈ v.asIdeal) :
    ∃ u ∈ intV E v, (q : E ⊗[F] v.adicCompletion F) * u = 1 := by
  have hq : (q : 𝓞 F) ∉ v.asIdeal := by
    intro hq
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hpq
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (a : 𝓞 F) * p + (b : 𝓞 F) * q = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 F) hab
    rw [← h1]
    exact add_mem (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hq)
  have hval : Valued.v (q : v.adicCompletion F) = 1 := by
    have hc : ∀ n : ℕ, ((n : F) : v.adicCompletion F) = (n : v.adicCompletion F) := by
      intro n
      induction n with
      | zero => rw [Nat.cast_zero, Nat.cast_zero, HeightOneSpectrum.adicCompletion.coe_zero]
      | succ n ih =>
        rw [Nat.cast_succ, Nat.cast_succ, ← ih, HeightOneSpectrum.adicCompletion.coe_add,
          HeightOneSpectrum.adicCompletion.coe_one]
    rw [← hc q, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      ← map_natCast (algebraMap (𝓞 F) F) q, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff]
    exact hq
  have hq0 : (q : v.adicCompletion F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hval; exact zero_ne_one hval
  refine ⟨(1 : E) ⊗ₜ[F] (q : v.adicCompletion F)⁻¹, ?_, ?_⟩
  · apply Subring.subset_closure
    refine Or.inr ⟨⟨_, ?_⟩, rfl⟩
    change Valued.v ((q : v.adicCompletion F)⁻¹) ≤ 1
    rw [map_inv₀, hval, inv_one]
  · rw [Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_inv_cancel₀ hq0, Algebra.TensorProduct.one_def]

theorem idem_eq_zero (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime) (hv : (p : 𝓞 F) ∈ v.asIdeal)
    {e : E ⊗[F] v.adicCompletion F} (he : e ∈ intV E v) (hee : e * e = e)
    (hd : ∃ t ∈ OAd F E, Formalism.UG.P.afsplitIE v e = (p : E ⊗[F] Ad F) * t) : e = 0 := by
  obtain ⟨t, ht, hte⟩ := hd
  have hprops := GlobalTheory.St.G.IntAd.integral_adeles_properties F E
  have hs : Formalism.UG.prV (E := E) v t ∈ intV E v := (hprops.1 t).1 ht v
  have hes : e = (p : E ⊗[F] v.adicCompletion F) * Formalism.UG.prV (E := E) v t := by
    have h1 := congrArg (Formalism.UG.prV (E := E) v) hte
    rwa [Formalism.UG.P.afsplit_prV_IE, map_mul, map_natCast] at h1
  have hidem : IsIdempotentElem e := hee
  have hpow : ∀ k : ℕ, e = (p : E ⊗[F] v.adicCompletion F) ^ (k + 1) *
      (Formalism.UG.prV (E := E) v t) ^ (k + 1) := fun k => by
    rw [← mul_pow, ← hes, hidem.pow_succ_eq]
  have hzero : Formalism.UG.P.afsplitIE v e = 0 := by
    refine hprops.2.2.1 _ fun m hm => ?_
    obtain ⟨k, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.one_lt.ne'
    obtain ⟨u, hu, hmu⟩ := exists_inv (E := E) v ((Nat.Prime.coprime_iff_not_dvd hp).2 hm') hv
    set s := Formalism.UG.prV (E := E) v t
    have hw : u * (p : E ⊗[F] v.adicCompletion F) * s ^ (k + 1) ∈ intV E v :=
      mul_mem (mul_mem hu (natCast_mem _ p)) (pow_mem hs _)
    have he' : e = ((p ^ k * m' : ℕ) : E ⊗[F] v.adicCompletion F) *
        (u * (p : E ⊗[F] v.adicCompletion F) * s ^ (k + 1)) := by
      calc e = ((m' : E ⊗[F] v.adicCompletion F) * u) * e := by rw [hmu, one_mul]
        _ = ((m' : E ⊗[F] v.adicCompletion F) * u) *
            ((p : E ⊗[F] v.adicCompletion F) ^ (k + 1) * s ^ (k + 1)) := by rw [← hpow k]
        _ = _ := by push_cast; ring
    refine ⟨Formalism.UG.P.afsplitIE v (u * (p : E ⊗[F] v.adicCompletion F) * s ^ (k + 1)),
      ie_mem v hw, ?_⟩
    conv_lhs => rw [he']
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have h2 := Formalism.UG.P.afsplit_prV_IE (E := E) v e
  rw [hzero, map_zero] at h2
  exact h2.symm

end Ad

end GlobalTheory.St.G.PsiLoc

open GlobalTheory.St.G.PsiLoc in

theorem GlobalTheory.St.G.psi_local_ne_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∀ x : E, psi (inclE (F := F) (Ad F) x) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1) → ∀ (p : ℕ), p.Prime → SplitsIn E p → ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → ∀ e ∈ intV E v, e * e = e → e ≠ 0 → ∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((p : F)⁻¹) * (e * a))) ≠ 1 := by
  intro F E _ _ _ _ _ _ cm psi hadd hint hrat p hp hsp v hv e he hee hne
  by_contra hcon
  push_neg at hcon
  apply hne
  have hprops := GlobalTheory.St.G.IntAd.integral_adeles_properties F E
  have hp0 : (p : E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hincl : ∀ y : 𝓞 E, inclE (F := F) (Ad F) (y : E) ∈ OAd F E := fun y =>
    (hprops.2.2.2.2 _).2 ⟨y, rfl⟩
  have hinclv : ∀ y : 𝓞 E, inclE (F := F) (v.adicCompletion F) (y : E) ∈ intV E v := fun y =>
    Subring.subset_closure (Or.inl ⟨⟨(y : E), ⟨y, rfl⟩⟩, rfl⟩)
  have hcv : algebraMap F (E ⊗[F] v.adicCompletion F) ((p : F)⁻¹) =
      inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) := by
    rw [Algebra.TensorProduct.algebraMap_apply, map_inv₀, map_natCast]
    rfl
  apply idem_eq_zero (E := E) v hp hv he hee
  obtain ⟨x, t, ht, hxt⟩ := hprops.2.1 _ (ie_mem v he) p hp.pos
  have htr : ∀ y : 𝓞 E, ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ E ((p : E)⁻¹ * x * y) := by
    intro y
    have key : psi (inclE (F := F) (Ad F) ((p : E)⁻¹ * x * y)) = 1 := by
      have h1 := hcon _ (hinclv y)
      have h2 : inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) *
          (e * inclE (F := F) (v.adicCompletion F) (y : E)) =
          e * Formalism.UG.prV (E := E) v (inclE (F := F) (Ad F) ((p : E)⁻¹ * y)) := by
        rw [Formalism.UG.P.afsplit_prV_inclE, map_mul]
        ring
      rw [hcv, h2, ie_mul_prV, hxt] at h1
      have hpp : inclE (F := F) (Ad F) (p : E) * inclE (F := F) (Ad F) ((p : E)⁻¹) = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hp0, map_one]
      have h3 : (inclE (F := F) (Ad F) (x : E) + (p : E ⊗[F] Ad F) * t) *
          inclE (F := F) (Ad F) ((p : E)⁻¹ * y) =
          inclE (F := F) (Ad F) ((p : E)⁻¹ * x * y) + t * inclE (F := F) (Ad F) (y : E) := by
        rw [← map_natCast (inclE (F := F) (Ad F)) p]
        simp only [map_mul]
        linear_combination (t * inclE (F := F) (Ad F) (y : E)) * hpp
      rw [h3, hadd, hint _ (mul_mem ht (hincl y)), mul_one] at h1
      exact h1
    have h4 := hrat ((p : E)⁻¹ * x * y)
    rw [key, one_mul, Complex.exp_eq_one_iff] at h4
    obtain ⟨n, hn⟩ := h4
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h5 : ((Algebra.trace ℚ E ((p : E)⁻¹ * x * y) : ℚ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      rw [hn]; ring
    exact_mod_cast h5.symm
  obtain ⟨z, hz⟩ := exists_eq_mul hp hsp x htr
  refine ⟨inclE (F := F) (Ad F) (z : E) + t, add_mem (hincl z) ht, ?_⟩
  rw [hxt, hz, map_mul, map_natCast]
  ring

end
