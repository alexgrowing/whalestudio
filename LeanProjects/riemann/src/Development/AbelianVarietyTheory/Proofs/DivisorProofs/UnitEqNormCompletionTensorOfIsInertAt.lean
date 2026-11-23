import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertUnitNorm

open IsDedekindDomain.HeightOneSpectrum Polynomial

theorem exists_root_quadratic_of_approx {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p q a₀ : v.adicCompletionIntegers F)
    (h₀ : Valued.v ((a₀ ^ 2 + p * a₀ + q : v.adicCompletionIntegers F) : v.adicCompletion F) < 1)
    (hd : IsUnit (2 * a₀ + p)) :
    ∃ a : v.adicCompletionIntegers F, a ^ 2 + p * a + q = 0 := by
  by_cases he0 : a₀ ^ 2 + p * a₀ + q = 0
  · exact ⟨a₀, he0⟩
  haveI := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).1 _ h₀
  haveI : HenselianRing (v.adicCompletionIntegers F) (Ideal.span {a₀ ^ 2 + p * a₀ + q}) :=
    IsAdicComplete.henselianRing _ _
  have hf : (X ^ 2 + C p * X + C q : (v.adicCompletionIntegers F)[X]).Monic := by monicity!
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := Ideal.span {a₀ ^ 2 + p * a₀ + q}) _ hf a₀
    (by simpa using Ideal.subset_span (Set.mem_singleton _)) (by
      have : eval a₀ (derivative (X ^ 2 + C p * X + C q : (v.adicCompletionIntegers F)[X])) = 2 * a₀ + p := by
        simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_pow, zero_mul, zero_add, mul_one, add_zero, eval_natCast, Nat.cast_ofNat]
        ring
      rw [this]; exact hd.map _)
  exact ⟨a, by simpa [IsRoot] using ha⟩

end GlobalTheory.InertUnitNorm

namespace GlobalTheory.InertUnitNorm

open IsDedekindDomain.HeightOneSpectrum Polynomial

theorem exists_ne_of_isCMExt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra h
  push_neg at h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : NumberField.ComplexEmbedding.IsReal τ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have h1 := hσ.2.2.2 τ x
    rw [h x] at h1
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]
    exact h1.symm
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (hσ.2.1.isComplex (NumberField.InfinitePlace.mk τ))) ⟨τ, hreal, rfl⟩

theorem exists_integral_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F))
    (hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime) :
    ∃ (a : 𝓞 E) (b c : 𝓞 F), ((a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0) ∧
      σ (a : E) = -algebraMap F E (b : F) - a ∧ ∀ r : 𝓞 F, r ^ 2 + b * r + c ∉ v.asIdeal := by
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  obtain ⟨a, ha⟩ := GlobalTheory.InertField.exists_not_congr h2 v
  have hi : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hmap : minpoly F (a : E) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hi
  have hdeg : (minpoly F (a : E)).natDegree = (minpoly (𝓞 F) a).natDegree := by
    rw [hmap, (minpoly.monic hi).natDegree_map]
  have hge : 2 ≤ (minpoly (𝓞 F) a).natDegree := by
    rw [minpoly.two_le_natDegree_iff hi]
    rintro ⟨r, hr⟩
    exact ha r (by rw [hr, sub_self]; exact zero_mem _)
  have hle : (minpoly F (a : E)).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le (a : E)
  have hnot : (a : E) ∉ (algebraMap F E).range :=
    (minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral _)).1 (hdeg ▸ hge)
  obtain ⟨b, c, hbc⟩ := isMonicOfDegree_two_iff.1
    (⟨by omega, minpoly.monic hi⟩ : IsMonicOfDegree (minpoly (𝓞 F) a) 2)
  have hq0 : a ^ 2 + algebraMap _ _ b * a + algebraMap _ _ c = 0 := by
    have := minpoly.aeval (𝓞 F) a
    rw [hbc] at this
    simpa using this
  have hq : (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 := by
    have := congrArg (algebraMap (𝓞 E) E) hq0
    simp only [map_add, map_mul, map_pow, map_zero] at this
    exact this
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro x hx
    exact hnot ⟨x, by rw [Algebra.algebraMap_eq_smul_one, hx]⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ⇑B = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hσa : σ (a : E) ≠ a := by
    intro hfix
    obtain ⟨x, hx⟩ := exists_ne_of_isCMExt σ hσ
    apply hx
    have : σ.toLinearMap = LinearMap.id := by
      refine B.ext fun i => ?_
      fin_cases i
      · simp [hB]
      · simp [hB, hfix]
    exact congrArg (fun f : E →ₗ[F] E => f x) this
  have hqσ : σ (a : E) ^ 2 + algebraMap F E (b : F) * σ a + algebraMap F E (c : F) = 0 := by
    have := congrArg σ hq
    simpa only [map_add, map_mul, map_pow, AlgHom.commutes, map_zero] using this
  have hconj : σ (a : E) = -algebraMap F E (b : F) - a := by
    have hm : (σ (a : E) - a) * (σ a + a + algebraMap F E (b : F)) = 0 := by
      linear_combination hqσ - hq
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd (sub_eq_zero.1 h) hσa
    · linear_combination h
  refine ⟨a, b, c, hq, hconj, fun r hr => ?_⟩
  have h1 := neg_mem (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hr)
  have e : -algebraMap (𝓞 F) (𝓞 E) (r ^ 2 + b * r + c) =
      (a - algebraMap _ _ r) * (a - algebraMap _ _ (-b - r)) := by
    simp only [map_add, map_mul, map_pow, map_sub, map_neg]
    linear_combination -hq0
  rw [e] at h1
  exact (hp.mem_or_mem h1).elim (ha _) (ha _)

end GlobalTheory.InertUnitNorm

namespace GlobalTheory.InertUnitNorm

open IsDedekindDomain.HeightOneSpectrum Polynomial

theorem exists_approx_mod {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (b c u₀ : 𝓞 F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hroot : ∀ r : 𝓞 F, r ^ 2 + b * r + c ∉ v.asIdeal)
    (hu : u₀ ∉ v.asIdeal) :
    ∃ r s : 𝓞 F, r ^ 2 - b * r * s + c * s ^ 2 - u₀ ∈ v.asIdeal ∧
      (2 * r - b * s ∉ v.asIdeal ∨ 2 * c * s - b * r ∉ v.asIdeal) := by
  classical
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  let π := Ideal.Quotient.mk v.asIdeal
  have hz : ∀ e : 𝓞 F, π e = 0 ↔ e ∈ v.asIdeal := fun e => Ideal.Quotient.eq_zero_iff_mem
  have h2k : (2 : 𝓞 F ⧸ v.asIdeal) ≠ 0 := by
    intro h
    exact h2 ((hz 2).1 (by rw [map_ofNat]; exact h))
  have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) % 2 = 1 := by
    by_contra hc
    have hc0 : Fintype.card (𝓞 F ⧸ v.asIdeal) % 2 = 0 := by omega
    have hch := FiniteField.even_card_iff_char_two.2 hc0
    haveI : CharP (𝓞 F ⧸ v.asIdeal) 2 := by rw [← hch]; exact ringChar.charP _
    exact h2k (by exact_mod_cast CharP.cast_eq_zero (𝓞 F ⧸ v.asIdeal) 2)
  obtain ⟨h, hh⟩ : ∃ h : 𝓞 F ⧸ v.asIdeal, 2 * h = 1 := ⟨2⁻¹, mul_inv_cancel₀ h2k⟩
  have hroot' : ∀ x : 𝓞 F ⧸ v.asIdeal, x ^ 2 + π b * x + π c ≠ 0 := by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hroot r ((hz _).1 (by simpa [π] using hx))
  have hD0 : π b ^ 2 - 4 * π c ≠ 0 := by
    intro h0
    apply hroot' (-(π b) * h)
    linear_combination (h ^ 2 - h) * h0 + π c * (2 * h - 1) * hh
  obtain ⟨s, ρ, hsρ⟩ := FiniteField.exists_root_sum_quadratic
    (f := X ^ 2) (g := -(C (π b ^ 2 - 4 * π c) * X ^ 2 + C (4 * π u₀)))
    (by simp) (by rw [degree_neg]; compute_degree!) hcard
  have hsρ' : s ^ 2 - ((π b ^ 2 - 4 * π c) * ρ ^ 2 + 4 * π u₀) = 0 := by
    simpa [sub_eq_add_neg] using hsρ
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (h * (s + π b * ρ))
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ρ
  have hr' : π r = h * (s + π b * ρ) := hr
  have ht' : π t = ρ := ht
  have hQ : π (r ^ 2 - b * r * t + c * t ^ 2 - u₀) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, hr', ht']
    linear_combination h ^ 2 * hsρ' + (h * s * π b * ρ + h * π b ^ 2 * ρ ^ 2 - (π c * ρ ^ 2 - π u₀) * (1 + 2 * h)) * hh
  refine ⟨r, t, (hz _).1 hQ, ?_⟩
  by_contra hboth
  push_neg at hboth
  have e1 := (hz _).2 hboth.1
  have e2 := (hz _).2 hboth.2
  simp only [map_sub, map_mul, map_ofNat] at e1 e2
  have hu' : π u₀ ≠ 0 := fun h0 => hu ((hz _).1 h0)
  apply mul_ne_zero h2k hu'
  simp only [map_sub, map_add, map_mul, map_pow] at hQ
  linear_combination π r * e1 + π t * e2 - 2 * hQ

end GlobalTheory.InertUnitNorm

namespace GlobalTheory.InertUnitNorm

open IsDedekindDomain.HeightOneSpectrum Polynomial

theorem mem_maximalIdeal_iff_valued_lt_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have : Valued.v (x : v.adicCompletion F) ≤ 1 := x.2
  constructor
  · intro h; exact lt_of_le_of_ne this h
  · intro h; exact h.ne

theorem algebraMap_mem_maximalIdeal_iff {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) e ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      e ∈ v.asIdeal := by
  rw [mem_maximalIdeal_iff_valued_lt_one, algebraMap_adicCompletionIntegers_apply,
    valuedAdicCompletion_eq_valuation', valuation_lt_one_iff_mem]

theorem coe_algebraMap_adicCompletionIntegers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : 𝓞 F) :
    ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) e : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (e : F) := by
  rw [algebraMap_adicCompletionIntegers_apply]
  rfl

end GlobalTheory.InertUnitNorm

namespace GlobalTheory.InertUnitNorm

open IsDedekindDomain.HeightOneSpectrum Polynomial

theorem exists_int_sol {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (b c : 𝓞 F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hroot : ∀ r : 𝓞 F, r ^ 2 + b * r + c ∉ v.asIdeal)
    (U : v.adicCompletionIntegers F) (hU : Valued.v (U : v.adicCompletion F) = 1) :
    ∃ x y : v.adicCompletionIntegers F,
      x ^ 2 - algebraMap (𝓞 F) _ b * x * y + algebraMap (𝓞 F) _ c * y ^ 2 = U := by
  set m := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) with hm
  let ι := algebraMap (𝓞 F) (v.adicCompletionIntegers F)
  have hιm : ∀ e : 𝓞 F, ι e ∈ m ↔ e ∈ v.asIdeal := algebraMap_mem_maximalIdeal_iff v
  have hιu : ∀ e : 𝓞 F, e ∉ v.asIdeal → IsUnit (ι e) := fun e he => by
    by_contra h
    exact he ((hιm e).1 ((IsLocalRing.mem_maximalIdeal _).2 h))
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.Idele.exists_valued_sub_le v (a := (U : v.adicCompletion F)) hU.le 1
  have hd : U - ι u₀ ∈ m := by
    rw [mem_maximalIdeal_iff_valued_lt_one]
    have : ((U - ι u₀ : v.adicCompletionIntegers F) : v.adicCompletion F) =
        (U : v.adicCompletion F) - algebraMap F _ (algebraMap (𝓞 F) F u₀) := by
      rw [AddSubgroupClass.coe_sub, coe_algebraMap_adicCompletionIntegers]
    rw [this]
    refine lt_of_le_of_lt hu₀ ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hUm : U ∉ m := by
    rw [mem_maximalIdeal_iff_valued_lt_one, hU]; exact lt_irrefl 1
  have hu₀v : u₀ ∉ v.asIdeal := by
    intro h
    apply hUm
    have := Ideal.add_mem m hd ((hιm u₀).2 h)
    rwa [sub_add_cancel] at this
  obtain ⟨r, s, hQ, hder⟩ := exists_approx_mod v b c u₀ h2 hroot hu₀v
  have hQm := (hιm _).2 hQ
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at hQm
  rcases hder with hA | hB
  · obtain ⟨a, ha⟩ := exists_root_quadratic_of_approx v (-(ι b * ι s)) (ι c * ι s ^ 2 - U) (ι r)
      (by
        rw [← mem_maximalIdeal_iff_valued_lt_one]
        have e : ι r ^ 2 + -(ι b * ι s) * ι r + (ι c * ι s ^ 2 - U) =
            (ι r ^ 2 - ι b * ι r * ι s + ι c * ι s ^ 2 - ι u₀) - (U - ι u₀) := by ring
        rw [e]
        exact Ideal.sub_mem _ hQm hd)
      (by
        have e : 2 * ι r + -(ι b * ι s) = ι (2 * r - b * s) := by
          simp only [map_sub, map_mul, map_ofNat]; ring
        rw [e]
        exact hιu _ hA)
    exact ⟨a, ι s, by linear_combination ha⟩
  · have hc : c ∉ v.asIdeal := by simpa using hroot 0
    obtain ⟨ci, hci⟩ := (hιu c hc).exists_right_inv
    obtain ⟨a, ha⟩ := exists_root_quadratic_of_approx v (-(ι b * ι r * ci)) ((ι r ^ 2 - U) * ci) (ι s)
      (by
        rw [← mem_maximalIdeal_iff_valued_lt_one]
        have e : ι s ^ 2 + -(ι b * ι r * ci) * ι s + (ι r ^ 2 - U) * ci =
            ci * ((ι r ^ 2 - ι b * ι r * ι s + ι c * ι s ^ 2 - ι u₀) - (U - ι u₀)) := by
          linear_combination (-(ι s) ^ 2) * hci
        rw [e]
        exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hQm hd))
      (by
        have e : 2 * ι s + -(ι b * ι r * ci) = ci * ι (2 * c * s - b * r) := by
          simp only [map_sub, map_mul, map_ofNat]
          linear_combination (-2 * ι s) * hci
        rw [e]
        exact (IsUnit.of_mul_eq_one (ι c) (by rw [mul_comm]; exact hci)).mul (hιu _ hB))
    exact ⟨ι r, a, by linear_combination (ι c) * ha + (ι b * ι r * a - (ι r ^ 2 - U)) * hci⟩

end GlobalTheory.InertUnitNorm

namespace GlobalTheory.InertUnitNorm

open IsDedekindDomain.HeightOneSpectrum Polynomial

theorem unit_eq_mul_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∀ u : Fv F v, Valued.v u = 1 →
      ∃ z : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) u = z * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ z := by
  intro F E _ _ _ _ _ σ B hB v w hvw _hfield u hu
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hconj, hroot⟩ := exists_integral_gen σ hB.cm v hp
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨x, y, hxy⟩ := exists_int_sol v b c h2 hroot ⟨u, hu.le⟩ hu
  have hK : (x : Fv F v) ^ 2 - algebraMap F (Fv F v) (b : F) * x * y +
      algebraMap F (Fv F v) (c : F) * y ^ 2 = u := by
    have := congrArg (fun t : v.adicCompletionIntegers F => (t : v.adicCompletion F)) hxy
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow, coe_algebraMap_adicCompletionIntegers] at this
    exact this
  let ι := algebraMap (Fv F v) (Fv F v ⊗[F] E)
  have hιF : ∀ t : F, ι (algebraMap F (Fv F v) t) = (1 : Fv F v) ⊗ₜ[F] algebraMap F E t := fun t => by
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  set α : Fv F v ⊗[F] E := (1 : Fv F v) ⊗ₜ[F] (a : E) with hα
  have hq' : α ^ 2 + ι (algebraMap F (Fv F v) (b : F)) * α + ι (algebraMap F (Fv F v) (c : F)) = 0 := by
    have := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E) hq
    rw [map_add, map_add, map_mul, map_pow, map_zero] at this
    rw [hιF, hιF]
    exact this
  have hσα : Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ α =
      -ι (algebraMap F (Fv F v) (b : F)) - α := by
    rw [hα, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hconj, hιF,
      TensorProduct.tmul_sub, TensorProduct.tmul_neg]
  refine ⟨ι x + ι y * α, ?_⟩
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσα]
  have hKι := congrArg ι hK
  simp only [map_add, map_sub, map_mul, map_pow] at hKι
  linear_combination (-1 : Fv F v ⊗[F] E) * hKι + ι y ^ 2 * hq'

end GlobalTheory.InertUnitNorm
