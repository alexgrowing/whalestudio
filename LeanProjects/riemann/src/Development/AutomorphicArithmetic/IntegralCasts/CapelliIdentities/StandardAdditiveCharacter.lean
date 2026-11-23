import Mathlib

open NumberField IsDedekindDomain Filter Topology
open scoped nonZeroDivisors

namespace UpperTheory.TraceAwayCharacter

private lemma trace_eq (F : Type) [Field F] [NumberField F] (x : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F x)
      = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (mixedEmbedding.latticeBasis F),
    Algebra.trace_eq_matrix_trace (integralBasis F)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mixedEmbedding.latticeBasis_apply, ← map_mul, mixedEmbedding.latticeBasis_repr_apply]

private lemma far (q : ℚ) (hq : ∀ z : ℤ, q ≠ z) :
    ∃ m : ℕ, (Complex.exp (-(2 * Real.pi * Complex.I) * ((((m : ℚ) * q : ℚ) : ℝ) : ℂ))).re ≤ 0 := by
  by_contra! h
  set z : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (q : ℂ)) with hz
  have hpow : ∀ m : ℕ, Complex.exp (-(2 * Real.pi * Complex.I) *
      ((((m : ℚ) * q : ℚ) : ℝ) : ℂ)) = z ^ m := by
    intro m
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz1 : z ≠ 1 := by
    intro h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    apply hq (-n)
    have h2 : (q : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (neg_ne_zero.mpr Complex.two_pi_I_ne_zero)
      rw [hn]
      push_cast
      ring
    exact_mod_cast h2
  have hd : z ^ q.den = 1 := by
    rw [← hpow, Rat.den_mul_eq_num, Complex.exp_eq_one_iff]
    refine ⟨-q.num, ?_⟩
    push_cast
    ring
  have hs : ∑ m ∈ Finset.range q.den, z ^ m = 0 := by
    rw [geom_sum_eq hz1, hd]
    simp
  have hpos : 0 < (∑ m ∈ Finset.range q.den, z ^ m).re := by
    rw [Complex.re_sum]
    refine Finset.sum_pos (fun m _ => hpow m ▸ h m) ?_
    exact Finset.nonempty_range_iff.mpr q.den_nz
  rw [hs] at hpos
  simp at hpos

private lemma exists_pole (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : F, (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F x ≤ 1) ∧ ¬ IsIntegral ℤ x := by
  obtain ⟨x, hx, hx1⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) v.ne_bot v.isPrime.ne_top
  refine ⟨x, fun u hu => ?_, fun hi => hx1 ?_⟩
  · have hle : ¬ v.asIdeal ≤ u.asIdeal := fun h =>
      hu (HeightOneSpectrum.ext (v.isMaximal.eq_of_le u.isPrime.ne_top h).symm)
    obtain ⟨t, ht, htu⟩ := Set.not_subset.mp hle
    have hv0 : (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot
    have h1 := (FractionalIdeal.mem_inv_iff hv0).mp hx (algebraMap _ F t)
      (FractionalIdeal.mem_coeIdeal_of_mem _ ht)
    obtain ⟨s, hs⟩ := (FractionalIdeal.mem_one_iff _).mp h1
    have h2 : u.valuation F (algebraMap _ F t) = 1 := by
      refine le_antisymm (u.valuation_le_one t) (not_lt.mp fun h => htu ?_)
      exact (u.valuation_lt_one_iff_mem t).mp h
    have h3 : u.valuation F (algebraMap (𝓞 F) F s) ≤ 1 := u.valuation_le_one s
    rwa [hs, map_mul, h2, mul_one] at h3
  · exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hi⟩, rfl⟩

private lemma exists_trace (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (N : ℕ) (hN : N ≠ 0) :
    ∃ y : F, (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F y ≤ 1) ∧
      ∀ z : ℤ, Algebra.trace ℚ F ((N : F) * y) ≠ z := by
  classical
  by_contra! h
  obtain ⟨x, hx, hxi⟩ := exists_pole F v
  let M : Submodule ℤ F :=
    AddSubgroup.toIntSubmodule
      { carrier := {a | ∃ y : F, (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F y ≤ 1) ∧
          a = (N : F) * y}
        add_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a + b, fun u hu => Valuation.map_add_le _ (ha u hu) (hb u hu), by ring⟩
        zero_mem' := ⟨0, by simp, by simp⟩
        neg_mem' := by
          rintro _ ⟨a, ha, rfl⟩
          exact ⟨-a, fun u hu => by simpa using ha u hu, by ring⟩ }
  have hM : ∀ a, a ∈ M ↔ ∃ y : F,
      (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F y ≤ 1) ∧ a = (N : F) * y :=
    fun _ => Iff.rfl
  have hle : M ≤ Submodule.span ℤ (Set.range ((Algebra.traceForm ℚ F).dualBasis
      (traceForm_nondegenerate ℚ F) (integralBasis F))) := by
    rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis]
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := (hM a).mp ha
    obtain ⟨c, rfl⟩ := (mem_span_integralBasis F).mp hb
    obtain ⟨z, hz⟩ := h (y * algebraMap _ F c) fun u hu => by
      rw [map_mul]
      exact mul_le_one' (hy u hu) (u.valuation_le_one c)
    refine Submodule.mem_one.mpr ⟨z, ?_⟩
    rw [Algebra.traceForm_apply, mul_assoc, hz]
    simp
  have hfg : M.FG := Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  refine hxi (isIntegral_of_smul_mem_submodule M ?_ hfg x ?_)
  · refine (Submodule.ne_bot_iff _).mpr ⟨(N : F), (hM _).mpr ⟨1, by simp, by simp⟩, ?_⟩
    exact_mod_cast hN
  · intro a ha
    obtain ⟨y, hy, rfl⟩ := (hM a).mp ha
    refine (hM _).mpr ⟨x * y, fun u hu => ?_, by rw [smul_eq_mul]; ring⟩
    rw [map_mul]
    exact mul_le_one' (hx u hu) (hy u hu)

private lemma tendsto_local (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (w : ℕ → u.adicCompletion F) (hw : ∀ n, Valued.v (w n) ≤ 1) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : u.adicCompletion F) * w n) atTop (𝓝 0) := by
  have hnat : ∀ m : ℕ, ((m : ℕ) : u.adicCompletion F) =
      algebraMap F (u.adicCompletion F) (algebraMap (𝓞 F) F (m : 𝓞 F)) := by
    intro m
    simp
  have hval : ∀ m : ℕ, Valued.v ((m : ℕ) : u.adicCompletion F) =
      u.valuation F (algebraMap (𝓞 F) F (m : 𝓞 F)) := by
    intro m
    rw [hnat]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _
  set p : ℕ := Ideal.absNorm u.asIdeal with hp
  have hp0 : p ≠ 0 := fun h => u.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hp1 : Valued.v ((p : ℕ) : u.adicCompletion F) < 1 := by
    rw [hval]
    exact (u.valuation_lt_one_iff_mem _).mpr (Ideal.absNorm_mem _)
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hp1
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff] at ht ⊢
  intro γ hγ
  obtain ⟨k, hk⟩ := (ht γ hγ).exists
  filter_upwards [eventually_ge_atTop (p ^ k)] with n hn
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero (pow_ne_zero k hp0)) hn
  refine lt_of_le_of_lt ?_ hk
  rw [hc, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul]
  refine mul_le_of_le_one_right' ?_
  rw [Valuation.restrict_le_one_iff, map_mul]
  refine mul_le_one' ?_ (hw n)
  rw [hval]
  exact u.valuation_le_one _

private lemma tendsto_finite (F : Type) [Field F] [NumberField F]
    (a : ℕ → FiniteAdeleRing (𝓞 F) F) (w : ∀ u : HeightOneSpectrum (𝓞 F), ℕ → u.adicCompletion F)
    (hw : ∀ u n, Valued.v (w u n) ≤ 1)
    (ha : ∀ u n, a n u = ((n.factorial : ℕ) : u.adicCompletion F) * w u n) :
    Tendsto a atTop (𝓝 0) := by
  have hmem : ∀ u n, a n u ∈ (u.adicCompletionIntegers F : Set (u.adicCompletion F)) := by
    intro u n
    rw [ha]
    exact mul_mem (natCast_mem (u.adicCompletionIntegers F) _) (hw u n)
  let b : ℕ → ∀ u : HeightOneSpectrum (𝓞 F),
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)) := fun n u => ⟨a n u, hmem u n⟩
  let b0 : ∀ u : HeightOneSpectrum (𝓞 F),
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)) :=
    fun u => ⟨0, zero_mem (u.adicCompletionIntegers F)⟩
  have hb : Tendsto b atTop (𝓝 b0) := by
    rw [tendsto_pi_nhds]
    intro u
    rw [tendsto_subtype_rng]
    simp only [b, b0, ha]
    exact tendsto_local F u (w u) (hw u)
  exact ((RestrictedProduct.isEmbedding_structureMap
    (R := fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
    (A := fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F)))
    (𝓕 := cofinite)).continuous.tendsto b0).comp hb

private lemma exists_away (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : F) : ∃ r : FiniteAdeleRing (𝓞 F) F,
      r v = 0 ∧ ∀ u, u ≠ v → r u = algebraMap F (u.adicCompletion F) x := by
  classical
  refine ⟨⟨fun u => if u = v then 0 else algebraMap F (u.adicCompletion F) x, ?_⟩, ?_, ?_⟩
  · filter_upwards [(algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2] with u hu
    split_ifs
    · exact zero_mem (u.adicCompletionIntegers F)
    · exact hu
  · exact if_pos rfl
  · exact fun u hu => if_neg hu

end UpperTheory.TraceAwayCharacter

open UpperTheory.TraceAwayCharacter in
theorem UpperTheory.standard_additive_character :
    ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ),
        Continuous ψ →
        (∀ x : F, ψ (algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) x) = 1) →
        (∀ a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F, a.2 = 0 →
          ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
            (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F)
              (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) : ℝ))) →
        ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          ∃ a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F,
            a.1 = 0 ∧ (∀ u, u ≠ v → a.2 u = 0) ∧ ψ a ≠ 1 := by
  intro F _ _ ψ hc hF hinf v
  classical
  by_contra! hv
  let j : FiniteAdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F := fun r => (0, r)
  have hj : Continuous j := continuous_const.prodMk continuous_id
  have key : ∀ (x : F) (r : FiniteAdeleRing (𝓞 F) F),
      (∀ u, u ≠ v → r u = algebraMap F (u.adicCompletion F) x) →
      ψ (-j r) = Complex.exp (-(2 * Real.pi * Complex.I) *
        (((Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ)) := by
    intro x r hr
    let i : AdeleRing (𝓞 F) F := (algebraMap F (InfiniteAdeleRing F) x, 0)
    let c : AdeleRing (𝓞 F) F := (0, r - algebraMap F (FiniteAdeleRing (𝓞 F) F) x)
    have h1 : ψ c = 1 := hv c rfl fun u hu => by
      change r u - algebraMap F (u.adicCompletion F) x = 0
      rw [hr u hu, sub_self]
    have h2 : i = -j r + c + algebraMap F (AdeleRing (𝓞 F) F) x := by
      refine Prod.ext ?_ ?_
      · change algebraMap F (InfiniteAdeleRing F) x
          = -0 + 0 + algebraMap F (InfiniteAdeleRing F) x
        ring
      · change 0 = -r + (r - algebraMap F (FiniteAdeleRing (𝓞 F) F) x)
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) x
        ring
    have h3 := hinf i rfl
    have h4 : InfiniteAdeleRing.ringEquiv_mixedSpace F i.1 = mixedEmbedding F x :=
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
    rw [h4, trace_eq, h2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1, hF, mul_one,
      mul_one] at h3
    exact h3
  have hy : ∀ n : ℕ, ∃ y : F, (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F y ≤ 1) ∧
      (Complex.exp (-(2 * Real.pi * Complex.I) *
        (((Algebra.trace ℚ F ((n.factorial : F) * y) : ℚ) : ℝ) : ℂ))).re ≤ 0 := by
    intro n
    obtain ⟨y, hy, hz⟩ := exists_trace F v n.factorial n.factorial_ne_zero
    obtain ⟨m, hm⟩ := far _ hz
    refine ⟨(m : F) * y, fun u hu => ?_, ?_⟩
    · rw [map_mul]
      refine mul_le_one' ?_ (hy u hu)
      have : u.valuation F (algebraMap (𝓞 F) F (m : 𝓞 F)) ≤ 1 := u.valuation_le_one _
      rwa [map_natCast] at this
    · rwa [mul_left_comm, ← nsmul_eq_mul m, map_nsmul, nsmul_eq_mul]
  choose y hy hre using hy
  choose r hr0 hr using fun n : ℕ => exists_away F v ((n.factorial : F) * y n)
  have ht : Tendsto r atTop (𝓝 0) := by
    refine tendsto_finite F r
      (fun u n => if u = v then 0 else algebraMap F (u.adicCompletion F) (y n)) ?_ ?_
    · intro u n
      split_ifs with hu
      · simp
      · exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).trans_le (hy n u hu)
    · intro u n
      split_ifs with hu
      · subst hu
        rw [hr0, mul_zero]
      · rw [hr n u hu, map_mul, map_natCast]
  have hcont : Continuous fun s => (ψ (-j s)).re :=
    Complex.continuous_re.comp (hc.comp hj.neg)
  have hlim := (hcont.tendsto 0).comp ht
  have h0 : (ψ (-j 0)).re = 1 := by
    have : j 0 = 0 := rfl
    rw [this, neg_zero, AddChar.map_zero_eq_one, Complex.one_re]
  rw [h0] at hlim
  have hle : (1 : ℝ) ≤ 0 := le_of_tendsto' hlim fun n => by
    change (ψ (-j (r n))).re ≤ 0
    rw [key _ _ (hr n)]
    exact hre n
  exact absurd hle (by norm_num)
