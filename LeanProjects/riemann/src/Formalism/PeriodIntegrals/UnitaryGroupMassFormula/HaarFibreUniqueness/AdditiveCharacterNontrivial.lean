import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SmulMemHermR
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement

noncomputable section

namespace PI.OmFibreUniq.W.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology
open scoped TensorProduct

theorem eq_one_of_pow_near (z : ℂ) (hz : ‖z‖ = 1) (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1) : z = 1 := by
  have key : ∀ w : ℂ, Complex.normSq w = 1 →
      Complex.normSq (w ^ 2 - 1) = Complex.normSq (w - 1) * (4 - Complex.normSq (w - 1)) := by
    intro w hw
    have e1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    have e2 : Complex.normSq (w + 1) = 4 - Complex.normSq (w - 1) := by
      rw [Complex.normSq_add, Complex.normSq_sub, hw, Complex.normSq_one]; ring
    rw [e1, Complex.normSq_mul, e2]
  have hn : ∀ m : ℕ, Complex.normSq (z ^ (2 ^ m)) = 1 := fun m => by
    rw [map_pow, Complex.normSq_eq_norm_sq, hz]; simp
  have hlt : ∀ m : ℕ, Complex.normSq (z ^ (2 ^ m) - 1) < 1 := fun m => by
    have := h (2 ^ m)
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z ^ 2 ^ m - 1)]
  have hge : ∀ m : ℕ, 3 ^ m * Complex.normSq (z - 1) ≤ Complex.normSq (z ^ (2 ^ m) - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : z ^ (2 ^ (m + 1)) = (z ^ (2 ^ m)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e, key _ (hn m), pow_succ]
      have h0 := Complex.normSq_nonneg (z ^ 2 ^ m - 1)
      have h1 := hlt m
      nlinarith
  by_contra hne
  have hpos : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / Complex.normSq (z - 1)) (by norm_num : (1 : ℝ) < 3)
  have h1 := hge m
  have h2 := hlt m
  have h3 : 1 < 3 ^ m * Complex.normSq (z - 1) := by
    rw [div_lt_iff₀ hpos] at hm; linarith
  linarith

theorem exists_pi (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : 𝓞 F, π ∈ v.asIdeal ∧ π ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → π ∉ w.asIdeal := by
  have hv0 : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  let P : nonZeroDivisors (Ideal (𝓞 F)) := ⟨v.asIdeal, hv0⟩
  let h := orderOf (ClassGroup.mk0 P)
  have hpos : 0 < h := orderOf_pos _
  have h1 : ClassGroup.mk0 (P ^ h) = 1 := by rw [map_pow]; exact pow_orderOf_eq_one _
  have hPh : ((P ^ h : nonZeroDivisors (Ideal (𝓞 F))) : Ideal (𝓞 F)) = v.asIdeal ^ h := by simp [P]
  have hprin : (v.asIdeal ^ h).IsPrincipal := by
    rw [← hPh]; exact (ClassGroup.mk0_eq_one_iff (P ^ h).2).1 h1
  obtain ⟨π, hπ⟩ := hprin
  refine ⟨π, ?_, ?_, ?_⟩
  · have : π ∈ v.asIdeal ^ h := by rw [hπ]; exact Ideal.mem_span_singleton_self π
    exact Ideal.pow_le_self hpos.ne' this
  · intro h0
    apply pow_ne_zero h v.ne_bot
    rw [hπ, h0]
    simp
  · intro w hw hπw
    have h2 : v.asIdeal ^ h ≤ w.asIdeal := by
      rw [hπ, Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]; exact hπw
    have hle : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le h2
    have heq : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top hle
    exact hw (HeightOneSpectrum.ext heq.symm)

theorem sum_re_eq_trace {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (t : F) :
    (∑ w : InfinitePlace F,
      (InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) t) w)).re) =
      ((Algebra.trace ℚ F t : ℚ) : ℝ) := by
  have e1 : ∀ w : InfinitePlace F,
      InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) t) w) = w.embedding t :=
    fun w => by simp
  simp only [e1]
  rw [← Complex.re_sum]
  let e : InfinitePlace F ≃ (F →+* ℂ) :=
    { toFun := fun w => w.embedding
      invFun := InfinitePlace.mk
      left_inv := fun w => InfinitePlace.mk_embedding w
      right_inv := fun φ =>
        InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ) }
  have h2 : ∑ w : InfinitePlace F, w.embedding t = ∑ φ : F →+* ℂ, φ t :=
    Fintype.sum_equiv e _ _ (fun w => rfl)
  have h3 : ∑ φ : F →+* ℂ, φ t = ∑ σ : F →ₐ[ℚ] ℂ, σ t :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun φ => rfl)
  rw [h2, h3, ← trace_eq_sum_embeddings (E := ℂ) (x := t)]
  simp

theorem af_add_apply {F : Type} [Field F] [NumberField F] (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (a + b) w = a w + b w := rfl

theorem af_sub_apply {F : Type} [Field F] [NumberField F] (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (a - b) w = a w - b w := rfl

theorem af_mul_apply {F : Type} [Field F] [NumberField F] (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (a * b) w = a w * b w := rfl

theorem af_natCast_apply {F : Type} [Field F] [NumberField F] (N : ℕ) (w : HeightOneSpectrum (𝓞 F)) :
    (N : Af F) w = (N : Fv F w) := rfl

open Classical in
theorem singleV_apply {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    (w : HeightOneSpectrum (𝓞 F)) : (singleV F v y) w = (Pi.single v y : ∀ w, Fv F w) w := rfl

theorem af_algebraMap_apply {F : Type} [Field F] [NumberField F] (r : F) (w : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (Af F) r) w = algebraMap F (Fv F w) r := rfl

theorem additive_character_nontrivial : PsiNT := by
  intro F _ _ ψ v hψ hstd hTR
  classical
  by_contra hcon
  push_neg at hcon

  let U : Set (Af F) := {y | ‖ψ (pairA F 0 y) - 1‖ < 1}
  have hc : Continuous (fun y : Af F => ψ (pairA F 0 y)) :=
    hψ.1.comp (continuous_const.prodMk continuous_id)
  have hU : U ∈ 𝓝 (0 : Af F) := by
    refine IsOpen.mem_nhds (isOpen_lt (continuous_norm.comp (hc.sub continuous_const))
      continuous_const) ?_
    show ‖ψ (pairA F 0 0) - 1‖ < 1
    have : pairA F 0 (0 : Af F) = 0 := rfl
    rw [this, AddChar.map_zero_eq_one]; simp
  obtain ⟨N, hN1, hNU⟩ := Formalism.L2.SG.Pf.top_nhds_basis F U hU
  have hA : ∀ u ∈ Formalism.UG.intAd F, ψ (pairA F 0 ((N : Af F) * u)) = 1 := by
    intro u hu
    apply eq_one_of_pow_near _ (hψ.2.1 _)
    intro k
    have hku : (k : Af F) * u ∈ Formalism.UG.intAd F := Subring.mul_mem _ (natCast_mem (Formalism.UG.intAd F) k) hu
    have h1 := hNU _ hku
    have e : ψ (pairA F 0 ((N : Af F) * ((k : Af F) * u))) =
        ψ (pairA F 0 ((N : Af F) * u)) ^ k := by
      rw [← AddChar.map_nsmul_eq_pow]
      congr 1
      refine Prod.ext ?_ ?_
      · change (0 : Ainf F) = k • (0 : Ainf F)
        rw [smul_zero]
      · change (N : Af F) * ((k : Af F) * u) = k • ((N : Af F) * u)
        rw [nsmul_eq_mul]
        ring
    rw [← e]; exact h1

  obtain ⟨π, hπv, hπ0, hπw⟩ := exists_pi F v
  set p : F := algebraMap (𝓞 F) F π with hp
  have hp0 : p ≠ 0 := by
    rw [hp]; exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hπ0
  have hint : ∀ (c : 𝓞 F) (j : ℕ) (w : HeightOneSpectrum (𝓞 F)), w ≠ v →
      w.valuation F (algebraMap (𝓞 F) F c * p⁻¹ ^ j) ≤ 1 := by
    intro c j w hw
    simp only [hp, map_mul, map_pow, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap]
    rw [HeightOneSpectrum.intValuation_eq_one_iff.2 (hπw w hw), inv_one, one_pow, mul_one]
    exact w.intValuation_le_one c

  have htr : ∀ (j : ℕ) (c : 𝓞 F), ∃ m : ℤ,
      Algebra.trace ℚ F ((N : F) * p⁻¹ ^ j * algebraMap (𝓞 F) F c) = m := by
    intro j c
    set r : F := algebraMap (𝓞 F) F c * p⁻¹ ^ j with hr
    set t : F := (N : F) * r with ht
    let u : Af F := algebraMap F (Af F) r - singleV F v (algebraMap F (Fv F v) r)
    have hu : u ∈ Formalism.UG.intAd F := by
      intro w
      by_cases hw : w = v
      · subst hw
        show (algebraMap F (Af F) r - singleV F w (algebraMap F (Fv F w) r)) w ∈ _
        rw [af_sub_apply, singleV_apply, Pi.single_eq_same, af_algebraMap_apply, sub_self]
        exact zero_mem _
      · show (algebraMap F (Af F) r - singleV F v (algebraMap F (Fv F v) r)) w ∈ _
        rw [af_sub_apply, singleV_apply, Pi.single_eq_of_ne hw, af_algebraMap_apply, sub_zero,
          HeightOneSpectrum.mem_adicCompletionIntegers]
        have := hint c j w hw
        rw [← hr] at this
        have e : Valued.v (algebraMap F (Fv F w) r) = w.valuation F r :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) r
        rw [e]; exact this
    have hdec : algebraMap F (Af F) t =
        singleV F v (algebraMap F (Fv F v) t) + (N : Af F) * u := by
      apply FiniteAdeleRing.ext
      intro w
      rw [af_add_apply, af_mul_apply, af_natCast_apply, singleV_apply, af_sub_apply, singleV_apply,
        af_algebraMap_apply, af_algebraMap_apply]
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same, Pi.single_eq_same, sub_self, mul_zero, add_zero]
      · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, zero_add, sub_zero, ht, map_mul,
          map_natCast]
    have h1 : ψ (algebraMap F (AF F) t) = 1 := hψ.2.2.1 t
    have h2 : algebraMap F (AF F) t = pairA F (algebraMap F (Ainf F) t) 0 +
        pairA F 0 (singleV F v (algebraMap F (Fv F v) t)) + pairA F 0 ((N : Af F) * u) := by
      show ((algebraMap F (Ainf F) t, algebraMap F (Af F) t) : AF F) = _
      rw [hdec]
      simp only [pairA]
      refine Prod.ext ?_ ?_
      · show algebraMap F (Ainf F) t = algebraMap F (Ainf F) t + 0 + 0
        simp
      · show singleV F v (algebraMap F (Fv F v) t) + (N : Af F) * u =
          0 + singleV F v (algebraMap F (Fv F v) t) + (N : Af F) * u
        simp
    rw [h2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul] at h1
    have h3 : ψ (pairA F 0 (singleV F v (algebraMap F (Fv F v) t))) = 1 := hcon _
    rw [h3, hA u hu, mul_one, mul_one] at h1
    have h4 := hstd (algebraMap F (Ainf F) t)
    rw [show psiInf F ψ (algebraMap F (Ainf F) t) = ψ (pairA F (algebraMap F (Ainf F) t) 0) from rfl,
      h1, sum_re_eq_trace] at h4
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h4.symm
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h5 : (((Algebra.trace ℚ F t : ℚ) : ℝ) : ℂ) = (n : ℂ) :=
      mul_left_cancel₀ hpi (by rw [hn]; ring)
    have ht' : (N : F) * p⁻¹ ^ j * algebraMap (𝓞 F) F c = t := by rw [ht, hr]; ring
    rw [ht']
    exact_mod_cast h5

  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral ℤ ℚ F
  have hD : Algebra.discr ℚ b ≠ 0 := Algebra.discr_not_zero_of_basis ℚ b
  have hmem : ∀ j : ℕ, ((N : F) * p⁻¹ ^ j) ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) := by
    intro j
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨m, hm⟩ := htr j c
    rw [Algebra.traceForm_apply, hm]
    exact ⟨m, by simp⟩
  have hβ : v.valuation F p < 1 := by
    rw [hp, HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_lt_one_iff_mem π).2 hπv
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hγ : v.valuation F ((Algebra.discr ℚ b : F) * N) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact mul_ne_zero (by exact_mod_cast hD) hN0
  obtain ⟨j, hj⟩ := exists_pow_lt₀ hβ (Units.mk0 _ hγ)
  have hI : IsIntegral ℤ (Algebra.discr ℚ b • (1 : F) * ((N : F) * p⁻¹ ^ j)) :=
    isIntegral_discr_mul_of_mem_traceDual (1 : Submodule (𝓞 F) F) hb
      (Submodule.mem_one.2 ⟨1, map_one _⟩) (hmem j)
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hI
  have hle : v.valuation F (Algebra.discr ℚ b • (1 : F) * ((N : F) * p⁻¹ ^ j)) ≤ 1 := by
    rw [← hy]; exact v.valuation_le_one y
  have hprod : Algebra.discr ℚ b • (1 : F) * ((N : F) * p⁻¹ ^ j) * p ^ j =
      (Algebra.discr ℚ b : F) * N := by
    rw [Algebra.smul_def, mul_one, mul_assoc, mul_assoc, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero j hp0), mul_one]
    rfl
  have hge : v.valuation F ((Algebra.discr ℚ b : F) * N) ≤ (v.valuation F p) ^ j := by
    rw [← hprod, map_mul, map_pow]
    exact mul_le_of_le_one_left' hle
  exact absurd hj (not_lt.2 hge)

end PI.OmFibreUniq.W.Sd
