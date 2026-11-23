import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

private theorem UpperTheory.sum_reAt_eq_trace' (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ∑ v : InfinitePlace F, reAt v x = (Algebra.trace ℚ F x : ℝ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
  have hbij : Function.Bijective (fun v : InfinitePlace F => v.embedding) := by
    constructor
    · intro v w h
      simpa [InfinitePlace.mk_embedding] using congrArg InfinitePlace.mk h
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := by
        have := IsTotallyReal.isReal (InfinitePlace.mk φ)
        rwa [InfinitePlace.isReal_mk_iff] at this
      exact ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal hr⟩
  have h2 : ∑ v : InfinitePlace F, v.embedding x = ∑ φ : F →+* ℂ, φ x :=
    Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
  have h3 : ∑ φ : F →+* ℂ, φ x = ∑ σ : F →ₐ[ℚ] ℂ, σ x :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have h4 : ((Algebra.trace ℚ F x : ℝ) : ℂ) = ∑ v : InfinitePlace F, v.embedding x := by
    rw [h2, h3, ← h1]; simp
  unfold reAt
  rw [← Complex.re_sum, ← h4, Complex.ofReal_re]

private theorem UpperTheory.mem_dual_of_valuation_le_different (F : Type) [Field F] [NumberField F] (x : F)
    (hx : ∀ v : Pl F, v.valuation F x ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) :
    x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
  classical
  have hdvd : ∀ v : Pl F,
      v.asIdeal ^ ordI v (differentIdeal ℤ (𝓞 F)) ∣ differentIdeal ℤ (𝓞 F) := by
    intro v
    unfold ordI
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr differentIdeal_ne_bot)
      v.associates_irreducible).mpr le_rfl
  have hD := coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hne : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)
  rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)), ← hD,
    FractionalIdeal.mem_inv_iff hne]
  intro y hy
  obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
  rw [FractionalIdeal.mem_one_iff]
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F (x * algebraMap (𝓞 F) F d) ?_
  intro v
  have h1 : v.intValuation d ≤ WithZero.exp (-(ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) :=
    (v.intValuation_le_pow_iff_dvd d _).mpr
      ((hdvd v).trans (Ideal.dvd_span_singleton.mpr hd))
  rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap]
  calc v.valuation F x * v.intValuation d
      ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ) *
          WithZero.exp (-(ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) := mul_le_mul' (hx v) h1
    _ = 1 := by rw [← WithZero.exp_add]; simp

private theorem UpperTheory.false_of_mem_dual_of_valuation_eq_different_succ (F : Type) [Field F] [NumberField F] (x : F) (w : Pl F)
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))
    (hw : w.valuation F x = WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1)) : False := by
  classical
  have hD := coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hne : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)
  rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)), ← hD,
    FractionalIdeal.mem_inv_iff hne] at hx
  have hnd : ¬ w.asIdeal ^ (ordI w (differentIdeal ℤ (𝓞 F)) + 1) ∣ differentIdeal ℤ (𝓞 F) := by
    unfold ordI
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr differentIdeal_ne_bot)
        w.associates_irreducible]
    omega
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨d, hd, hd'⟩ := SetLike.not_le_iff_exists.mp hnd
  have hint := hx _ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩)
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hint
  have h1 : w.valuation F x * w.intValuation d ≤ 1 := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F), ← map_mul, ← ha,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact w.intValuation_le_one a
  apply hd'
  rw [← w.intValuation_le_pow_iff_mem]
  rw [hw] at h1
  calc w.intValuation d
      = WithZero.exp (-((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1)) *
          (WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1) * w.intValuation d) := by
        rw [← mul_assoc, ← WithZero.exp_add]; simp
    _ ≤ WithZero.exp (-((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1)) * 1 := mul_le_mul' le_rfl h1
    _ = WithZero.exp (-((ordI w (differentIdeal ℤ (𝓞 F)) + 1 : ℕ) : ℤ)) := by push_cast; simp

private theorem UpperTheory.mem_dual_one_iff_trace_mul_int (F : Type) [Field F] [NumberField F] (x : F) :
    x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ↔
      ∀ b : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (x * b) = n := by
  rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 F)) F) _ _ _)]
  constructor
  · intro h b
    obtain ⟨n, hn⟩ := h _ ((FractionalIdeal.mem_one_iff _).mpr ⟨b, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    simpa using hn.symm
  · intro h a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := h b
    exact ⟨n, by rw [Algebra.traceForm_apply, hn]; simp⟩

private theorem UpperTheory.cexp_two_pi_I_mul_eq_one_iff_int (t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (t : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      rw [hn]; ring
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

theorem UpperTheory.addChar_inverseDifferent_and_residue_sum_eq_zero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (η : F), ((∀ v : Pl F, v.valuation F η ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) → ∀ b : 𝓞 F, Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v (η * (b : F)) : ℂ)) = 1) ∧ ∀ (w : Pl F) [Fintype (𝓞 F ⧸ w.asIdeal)] (s : 𝓞 F ⧸ w.asIdeal → 𝓞 F), (∀ r, Ideal.Quotient.mk w.asIdeal (s r) = r) → (∀ v : Pl F, v ≠ w → v.valuation F η ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) → w.valuation F η = WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1) → ∑ r, Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v (η * (s r : F)) : ℂ)) = 0 := by
  intro F _ _ _ η
  have key : ∀ x : F, (∃ n : ℤ, Algebra.trace ℚ F x = n) ↔
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v x : ℂ)) = 1 := by
    intro x
    rw [← Complex.ofReal_sum, UpperTheory.sum_reAt_eq_trace', UpperTheory.cexp_two_pi_I_mul_eq_one_iff_int]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [hn]; push_cast; rfl⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by exact_mod_cast hn⟩
  have part1 : ∀ x : F, (∀ v : Pl F, v.valuation F x ≤
      WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) → ∀ b : 𝓞 F,
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v (x * (b : F)) : ℂ)) = 1 := by
    intro x hx b
    exact (key _).mp ((UpperTheory.mem_dual_one_iff_trace_mul_int F x).mp (UpperTheory.mem_dual_of_valuation_le_different F x hx) b)
  refine ⟨part1 η, ?_⟩
  intro w _ s hs hv hw
  set ψ : 𝓞 F → ℂ := fun b =>
    Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v (η * (b : F)) : ℂ)) with hψ
  have hadd : ∀ a b : 𝓞 F, ψ (a + b) = ψ a * ψ b := by
    intro a b
    simp only [hψ, ← Complex.exp_add]
    congr 1
    have e : ∀ v : InfinitePlace F, (reAt v (η * ((a + b : 𝓞 F) : F)) : ℂ) =
        (reAt v (η * (a : F)) : ℂ) + (reAt v (η * (b : F)) : ℂ) := by
      intro v
      simp only [reAt, map_add, mul_add, Complex.add_re, Complex.ofReal_add]
    rw [Finset.sum_congr rfl (fun v _ => e v), Finset.sum_add_distrib]
    ring
  have hker : ∀ c ∈ w.asIdeal, ψ c = 1 := by
    intro c hc
    have h := part1 (η * (c : F)) ?_ 1
    · simpa [hψ] using h
    intro v
    have hcv : v.valuation F (c : F) = v.intValuation c :=
      HeightOneSpectrum.valuation_of_algebraMap (K := F) v c
    by_cases hvw : v = w
    · subst hvw
      rw [map_mul, hw, hcv]
      have hc1 : v.intValuation c ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
        (v.intValuation_le_pow_iff_mem c 1).mpr (by simpa using hc)
      calc _ ≤ WithZero.exp ((ordI v (differentIdeal ℤ (𝓞 F)) : ℤ) + 1) *
            WithZero.exp (-((1 : ℕ) : ℤ)) := mul_le_mul' le_rfl hc1
        _ = _ := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    · rw [map_mul, hcv]
      calc _ ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ) * 1 :=
            mul_le_mul' (hv v hvw) (v.intValuation_le_one c)
        _ = _ := mul_one _
  have hcoset : ∀ a b : 𝓞 F, a - b ∈ w.asIdeal → ψ a = ψ b := by
    intro a b hab
    have e : a = b + (a - b) := by ring
    rw [e, hadd, hker _ hab, mul_one]
  obtain ⟨b0, hb0⟩ : ∃ b0 : 𝓞 F, ψ b0 ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hdual := (UpperTheory.mem_dual_one_iff_trace_mul_int F η).mpr (fun b => (key _).mpr (hcon b))
    exact UpperTheory.false_of_mem_dual_of_valuation_eq_different_succ F η w hdual hw
  have hsum : ψ b0 * ∑ r, ψ (s r) = ∑ r, ψ (s r) := by
    rw [Finset.mul_sum]
    calc ∑ r, ψ b0 * ψ (s r) = ∑ r, ψ (s (r + Ideal.Quotient.mk w.asIdeal b0)) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [← hadd]
          apply hcoset
          rw [← Ideal.Quotient.eq]
          simp only [map_add, hs]
          ring
      _ = ∑ r, ψ (s r) := Fintype.sum_equiv (Equiv.addRight _) _ _ (fun _ => rfl)
  have h0 : (ψ b0 - 1) * ∑ r, ψ (s r) = 0 := by rw [sub_mul, hsum, one_mul, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hb0
  · exact h
