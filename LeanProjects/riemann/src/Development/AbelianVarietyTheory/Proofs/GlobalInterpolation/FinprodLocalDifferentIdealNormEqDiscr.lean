import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.LocalDifferentProduct

section Local

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
theorem _root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap (x : 𝓞 K) :
    Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = v.intValuation x := by
  simp [valuation_of_algebraMap]

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma valued_le_of_mem_map_of_le_pow {I : Ideal (𝓞 K)} {n : ℕ} (hIn : I ≤ v.asIdeal ^ n)
    {x : v.adicCompletionIntegers K} (hx : x ∈ I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) :
    Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap]
    exact (intValuation_le_pow_iff_mem v i n).mpr (hIn hi)
  | zero => simp
  | add y z _ _ hy hz =>
    push_cast
    exact Valuation.map_add_le _ hy hz
  | smul a y _ hy =>
    rw [smul_eq_mul]
    push_cast
    rw [Valuation.map_mul]
    calc Valued.v (a : v.adicCompletion K) * Valued.v (y : v.adicCompletion K)
        ≤ 1 * WithZero.exp (-(n : ℤ)) := mul_le_mul' (a.2 : Valued.v (a : v.adicCompletion K) ≤ 1) hy
      _ = _ := one_mul _

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma exists_notMem_mul_mem_of_pow_count {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∃ s : 𝓞 K, s ∉ v.asIdeal ∧
      ∀ a ∈ v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors, a * s ∈ I := by
  set n := (Associates.mk v.asIdeal).count (Associates.mk I).factors
  obtain ⟨J, hJ⟩ : v.maxPowDividing I ∣ I := Ideal.dvd_iff_le.mpr (by
    rw [← Ideal.dvd_iff_le]
    exact (Associates.mk_le_mk_iff_dvd).mp (by
      rw [maxPowDividing, Associates.mk_pow]
      exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
        v.associates_irreducible).mpr le_rfl))
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle
    have h1 : v.asIdeal ^ (n + 1) ∣ I := by
      rw [Ideal.dvd_iff_le, hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    have h2 := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
      v.associates_irreducible).mp (by
        rw [← Associates.mk_pow]
        exact Associates.mk_le_mk_iff_dvd.mpr h1)
    omega
  obtain ⟨s, hsJ, hsv⟩ := SetLike.not_le_iff_exists.mp hJv
  refine ⟨s, hsv, fun a ha => ?_⟩
  rw [hJ]
  exact Ideal.mul_mem_mul ha hsJ

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma mem_map_adicCompletionIntegers_of_valued_le {I : Ideal (𝓞 K)} (hI : I ≠ 0) {y : v.adicCompletionIntegers K}
    (hy : Valued.v (y : v.adicCompletion K) ≤
      WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ))) :
    y ∈ I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) := by
  set n := (Associates.mk v.asIdeal).count (Associates.mk I).factors
  obtain ⟨s, hsv, hs⟩ := exists_notMem_mul_mem_of_pow_count v hI
  obtain ⟨π, hπ⟩ := intValuation_exists_uniformizer v
  have hπn : v.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hs1 : v.intValuation s = 1 :=
    le_antisymm (v.intValuation_le_one s) (not_lt.mp fun h => hsv ((intValuation_lt_one_iff_mem v s).mp h))
  have hi₀ : π ^ n * s ∈ I := hs _ ((intValuation_le_pow_iff_mem v _ n).mp hπn.le)
  have hval : Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (π ^ n * s) :
      v.adicCompletionIntegers K) : v.adicCompletion K) = WithZero.exp (-(n : ℤ)) := by
    rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap, map_mul, hπn, hs1, mul_one]
  set i₀ : v.adicCompletion K := ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (π ^ n * s) :
      v.adicCompletionIntegers K) : v.adicCompletion K) with hi₀def
  have hne : i₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hval
    exact WithZero.zero_ne_coe hval
  have hz : (y : v.adicCompletion K) / i₀ ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, map_div₀, hval]
    exact div_le_one_of_le₀ hy zero_le'
  have hy' : y = algebraMap (𝓞 K) (v.adicCompletionIntegers K) (π ^ n * s) * ⟨_, hz⟩ := by
    apply Subtype.ext
    show (y : v.adicCompletion K) = i₀ * ((y : v.adicCompletion K) / i₀)
    field_simp
  rw [hy']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hi₀)

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma exists_integer_valuation_sub_le_exp_neg (k : K) (hk : v.valuation K k ≤ 1) (n : ℕ) :
    ∃ a : 𝓞 K, v.valuation K (k - algebraMap (𝓞 K) K a) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hspan : Ideal.span {c} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨s, hsv, hs⟩ := exists_notMem_mul_mem_of_pow_count v hspan
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by
    simpa using hc0
  have hb : b ∈ v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {c})).factors := by
    rw [← intValuation_le_pow_iff_mem, ← intValuation_if_neg v hc0]
    rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap] at hk
    have hcv : v.intValuation c ≠ 0 := by
      rw [intValuation_if_neg v hc0]
      exact WithZero.exp_ne_zero
    exact (div_le_one₀ (zero_lt_iff.mpr hcv)).mp hk
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp (hs b hb)
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv v.isMaximal hsv
  refine ⟨a' * (y * ∑ j ∈ Finset.range n, i ^ j), ?_⟩
  have hgeom := mul_neg_geom_sum i n
  have hk' : algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c -
      algebraMap (𝓞 K) K (a' * (y * ∑ j ∈ Finset.range n, i ^ j)) =
      algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c * algebraMap (𝓞 K) K (i ^ n) := by
    have h1 : algebraMap (𝓞 K) K a' * algebraMap (𝓞 K) K c =
        algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K s := by
      rw [← map_mul, ← map_mul, ha']
    have h2 : algebraMap (𝓞 K) K y * algebraMap (𝓞 K) K s =
        1 - algebraMap (𝓞 K) K i := by
      rw [← map_mul, ← map_one (algebraMap (𝓞 K) K), ← map_sub, ← hyi]
      ring_nf
    have h3 := congrArg (algebraMap (𝓞 K) K) hgeom
    simp only [map_mul, map_sub, map_one, map_pow, map_sum] at h3 ⊢
    have key : algebraMap (𝓞 K) K b - algebraMap (𝓞 K) K c * (algebraMap (𝓞 K) K a' *
        (algebraMap (𝓞 K) K y * ∑ j ∈ Finset.range n, algebraMap (𝓞 K) K i ^ j)) =
        algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K i ^ n := by
      linear_combination (-(algebraMap (𝓞 K) K y *
          ∑ j ∈ Finset.range n, algebraMap (𝓞 K) K i ^ j)) * h1 -
        (algebraMap (𝓞 K) K b * ∑ j ∈ Finset.range n, algebraMap (𝓞 K) K i ^ j) * h2 -
        algebraMap (𝓞 K) K b * h3
    field_simp
    linear_combination key
  rw [hk', map_mul, valuation_of_algebraMap]
  calc v.valuation K (algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c) * v.intValuation (i ^ n)
      ≤ 1 * WithZero.exp (-(n : ℤ)) :=
        mul_le_mul' hk ((intValuation_le_pow_iff_mem v _ n).mpr (Ideal.pow_mem_pow hi n))
    _ = _ := one_mul _

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma exists_integer_valued_sub_le_exp_neg (x : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ a : 𝓞 K, Valued.v ((x : v.adicCompletion K) -
      ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
        v.adicCompletion K)) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := intValuation_exists_uniformizer v
  set z : v.adicCompletion K := ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (π ^ n) :
    v.adicCompletionIntegers K) : v.adicCompletion K)
  have hvz : Valued.v z = WithZero.exp (-(n : ℤ)) := by
    rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap, map_pow, hπ,
      ← WithZero.exp_nsmul]
    congr 1
    simp
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hvz
    exact WithZero.zero_ne_coe hvz
  have hnhds : {y : v.adicCompletion K | Valued.v ((x : v.adicCompletion K) - y) ≤
      WithZero.exp (-(n : ℤ))} ∈ nhds (x : v.adicCompletion K) := by
    have ho := Valued.isOpen_closedBall (v.adicCompletion K)
      ((Valuation.ne_zero_iff Valued.v.restrict).mpr hz0)
    have hc : Continuous fun y : v.adicCompletion K => (x : v.adicCompletion K) - y :=
      continuous_const.sub continuous_id
    refine Filter.mem_of_superset ((ho.preimage hc).mem_nhds ?_) ?_
    · show Valued.v.restrict ((x : v.adicCompletion K) - x) ≤ _
      rw [sub_self, map_zero]
      exact zero_le'
    · intro y hy
      rw [Set.mem_setOf_eq, ← hvz]
      exact (Valuation.restrict_le_iff Valued.v).mp hy
  obtain ⟨_, hz, ⟨k, rfl⟩⟩ := mem_closure_iff_nhds.mp
    ((denseRange_algebraMap (K := K) v) (x : v.adicCompletion K)) _ hnhds
  simp only [Set.mem_setOf_eq] at hz
  have hk1 : v.valuation K k ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have hle : WithZero.exp (-(n : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have h := Valuation.map_sub_le _ hx1 (hz.trans hle)
    rw [sub_sub_cancel] at h
    have e : algebraMap K (v.adicCompletion K) k = (k : v.adicCompletion K) := rfl
    rw [e] at h
    simpa using h
  obtain ⟨a, ha⟩ := exists_integer_valuation_sub_le_exp_neg v k hk1 n
  refine ⟨a, ?_⟩
  have e1 : ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) := rfl
  have hsplit : (x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) =
      ((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) k) +
      algebraMap K (v.adicCompletion K) (k - algebraMap (𝓞 K) K a) := by
    rw [map_sub]
    ring
  rw [e1, hsplit]
  refine Valuation.map_add_le _ hz ?_
  have e2 : algebraMap K (v.adicCompletion K) (k - algebraMap (𝓞 K) K a) =
      ((k - algebraMap (𝓞 K) K a : K) : v.adicCompletion K) := rfl
  rw [e2, valuedAdicCompletion_eq_valuation']
  exact ha

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in

theorem _root_.GlobalTheory.LocalDifferentProduct.card_quot_map {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) =
      Ideal.absNorm (v.maxPowDividing I) := by
  set n := (Associates.mk v.asIdeal).count (Associates.mk I).factors
  have hIn : I ≤ v.asIdeal ^ n := by
    rw [← Ideal.dvd_iff_le]
    exact (Associates.mk_le_mk_iff_dvd).mp (by
      rw [Associates.mk_pow]
      exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
        v.associates_irreducible).mpr le_rfl)
  let f : 𝓞 K →+* v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))
  have hker : RingHom.ker f = v.asIdeal ^ n := by
    ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h
      have h' := valued_le_of_mem_map_of_le_pow v hIn h
      rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap] at h'
      exact (intValuation_le_pow_iff_mem v a n).mp h'
    · intro h
      apply mem_map_adicCompletionIntegers_of_valued_le v hI
      rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap]
      exact (intValuation_le_pow_iff_mem v a n).mpr h
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := exists_integer_valued_sub_le_exp_neg v x n
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq]
    apply mem_map_adicCompletionIntegers_of_valued_le v hI
    rw [Valuation.map_sub_swap] at ha
    exact_mod_cast ha
  change _ = Ideal.absNorm (v.asIdeal ^ n)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv.symm

end Local

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in

theorem _root_.GlobalTheory.LocalDifferentProduct.finprod_card_quot_map {K : Type} [Field K] [NumberField K] {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K)))).Finite ∧
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) = Ideal.absNorm I := by
  have hcard : ∀ v : HeightOneSpectrum (𝓞 K), Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) = Ideal.absNorm (v.maxPowDividing I) :=
    fun v => _root_.GlobalTheory.LocalDifferentProduct.card_quot_map v hI
  simp_rw [hcard]
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I).Finite :=
    Ideal.finite_mulSupport hI
  refine ⟨hfin.subset (Function.mulSupport_comp_subset (map_one _) _), ?_⟩
  have h := MonoidHom.map_finprod (Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ).toMonoidHom hfin
  simp only [MonoidWithZeroHom.toMonoidHom_coe, Ideal.finprod_heightOneSpectrum_factorization hI] at h
  exact h.symm

section Relative

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

end Relative

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in

theorem _root_.GlobalTheory.LocalDifferentProduct.prod_normDifferentV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → (∀ x : E, star x = σ x) →
    _root_.Formalism.HermitianLatticesTheory.IsCMUnram E → (Function.mulSupport (_root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.normDifferentV F)).Finite ∧
      ((∏ᶠ v, _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.normDifferentV F v : ℕ) : ℝ) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr F ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr F = (2 * _root_.Formalism.HermitianLatticesTheory.vInv E) ^ _root_.Formalism.HermitianLatticesTheory.fDeg E := by
  intro F E _ _ _ _ _ _ σ hcm hstar hun
  have hD : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h := _root_.GlobalTheory.LocalDifferentProduct.finprod_card_quot_map hD
  have h2 : ∏ᶠ v, _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.normDifferentV F v = Ideal.absNorm (differentIdeal ℤ (𝓞 F)) := h.2
  refine ⟨h.1, ?_, ?_⟩
  · rw [h2, NumberField.absNorm_differentIdeal F (𝓞 F)]
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr, Nat.cast_natAbs]
  · have hrank : Module.finrank F E = 2 := hcm.2.2.1
    have hD1 : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨θ, t, ht, hθt⟩ := hun.2.2 P hP
      have hσ : σ (algebraMap (𝓞 E) E θ) = algebraMap (𝓞 E) E t := by rw [ht, hstar]
      set x : E := algebraMap (𝓞 E) E θ with hx
      have hxσ : x - σ x = algebraMap (𝓞 E) E (θ - t) := by rw [hσ, map_sub]
      have hxσ0 : x - σ x ≠ 0 := by
        rw [hxσ]
        intro h
        apply hθt
        rw [(map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h]
        exact P.zero_mem
      have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
      have hdeg : (minpoly F x).natDegree = 2 := by
        have h1 := minpoly.natDegree_le (A := F) x
        rw [hrank] at h1
        have h0 := minpoly.natDegree_pos hint
        have hne1 : (minpoly F x).natDegree ≠ 1 := by
          intro h
          obtain ⟨f, hf⟩ := minpoly.natDegree_eq_one_iff.mp h
          apply hxσ0
          rw [← hf, AlgHom.commutes, sub_self]
        omega
      have htopF : IntermediateField.adjoin F {x} = ⊤ := by
        refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
        rw [IntermediateField.adjoin.finrank hint, hdeg, IntermediateField.finrank_top', hrank]
      have htop : Algebra.adjoin F {x} = ⊤ := by
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htopF,
          IntermediateField.top_toSubalgebra]
      have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F E θ htop
      have hfac : (minpoly F x).map (algebraMap F E) = (X - C x) * (X - C (σ x)) := by
        set q := (minpoly F x).map (algebraMap F E) with hqdef
        have hq : q.IsRoot x := by
          rw [IsRoot, hqdef, eval_map_algebraMap, minpoly.aeval]
        have hqσ : q.IsRoot (σ x) := by
          rw [IsRoot, hqdef, eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
        set r := q /ₘ (X - C x) with hrdef
        have hqr : (X - C x) * r = q := mul_divByMonic_eq_iff_isRoot.mpr hq
        have hqmonic : q.Monic := (minpoly.monic hint).map _
        have hrmonic : r.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C x) (hqr ▸ hqmonic)
        have hrdeg : r.natDegree = 1 := by
          rw [hrdef, natDegree_divByMonic _ (monic_X_sub_C x), natDegree_X_sub_C, hqdef,
            natDegree_map, hdeg]
        have hr := hrmonic.eq_X_add_C hrdeg
        have hrσ : r.eval (σ x) = 0 := by
          have h := hqσ
          rw [IsRoot, ← hqr, eval_mul, eval_sub, eval_X, eval_C] at h
          exact (mul_eq_zero.mp h).resolve_left (by
            intro h'
            apply hxσ0
            rw [← neg_sub, h', neg_zero])
        have hc0 : r.coeff 0 = -σ x := by
          rw [hr, eval_add, eval_X, eval_C] at hrσ
          linear_combination hrσ
        rw [← hqr, hr, hc0, C_neg, ← sub_eq_add_neg]
      have hθint : IsIntegral (𝓞 F) x :=
        (Algebra.IsIntegral.isIntegral (R := 𝓞 F) θ).map (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E)
      have hmapE : (minpoly (𝓞 F) θ).map (algebraMap (𝓞 F) E) = (X - C x) * (X - C (σ x)) := by
        rw [← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 E) E) θ, ← hx,
          IsScalarTower.algebraMap_eq (𝓞 F) F E, ← Polynomial.map_map,
          ← minpoly.isIntegrallyClosed_eq_field_fractions' F hθint, hfac]
      have hval : algebraMap (𝓞 E) E (aeval θ (derivative (minpoly (𝓞 F) θ))) = x - σ x := by
        rw [← aeval_algebraMap_apply, ← hx, ← eval_map_algebraMap, ← derivative_map, hmapE]
        simp [derivative_mul]
      have hder : aeval θ (derivative (minpoly (𝓞 F) θ)) = θ - t :=
        FaithfulSMul.algebraMap_injective (𝓞 E) E (by rw [hval, hxσ])
      exact hθt (hder ▸ hle hmem)
    have hnat : (discr E).natAbs = (discr F).natAbs ^ 2 := by
      rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E),
        hD1, Ideal.absNorm_top, one_mul, hrank]
    have hE : |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
      have h' : ((discr E).natAbs : ℝ) = ((discr F).natAbs : ℝ) ^ 2 := by exact_mod_cast hnat
      rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs] at h'
      exact h'
    have hN : (0 : ℝ) < Fintype.card (InfinitePlace E) := by
      exact_mod_cast Fintype.card_pos
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr _root_.Formalism.HermitianLatticesTheory.vInv _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [hE, mul_div_cancel₀ _ (two_ne_zero' ℝ), ← Real.rpow_natCast _ (Fintype.card (InfinitePlace E)),
      ← Real.rpow_natCast |(discr F : ℝ)| 2, ← Real.rpow_mul (abs_nonneg _),
      ← Real.rpow_mul (abs_nonneg _)]
    have hexp : ((2 : ℕ) : ℝ) * (1 / (2 * (Fintype.card (InfinitePlace E) : ℝ))) *
        (Fintype.card (InfinitePlace E) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [hexp, Real.rpow_one]

end GlobalTheory.LocalDifferentProduct
