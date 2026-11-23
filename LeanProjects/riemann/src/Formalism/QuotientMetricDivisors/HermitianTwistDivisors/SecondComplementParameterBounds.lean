import Mathlib
import Formalism.QuotientMetricDivisors.Complement2Normaliser
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula

open Module NumberField IsDedekindDomain Finset

noncomputable section

namespace Formalism.DivisionValues

namespace PlaceSumConjugation

section Places

variable {K : Type} [Field K] [NumberField K]

theorem natCast_ne_zero' {g : ℕ} (hg : 0 < g) : (g : K) ≠ 0 := by
  exact_mod_cast hg.ne'

theorem vw_nat_nonneg (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ vw w (g : K) := by
  unfold vw
  have h : (g : K) = algebraMap (𝓞 K) K (g : 𝓞 K) := by simp
  rw [h, ← FractionalIdeal.coeIdeal_span_singleton]
  apply FractionalIdeal.count_coe_nonneg

theorem plOver_finite (g : ℕ) : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite := by
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    convert Set.finite_empty
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    unfold PlOver vw
    first | simp [FractionalIdeal.count_zero] | (unfold FractionalIdeal.count; simp)
  · have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (g : K) ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact natCast_ne_zero' hg
    have hfin := FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (g : K))
    have hsub : {w : HeightOneSpectrum (𝓞 K) | PlOver g w} ⊆ {v | FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (g : K)) ≠ 0} := by
      intro w hw
      simp only [Set.mem_setOf_eq] at hw ⊢
      unfold PlOver vw at hw
      exact hw.ne'
    first | exact (Filter.eventually_cofinite.mp hfin).subset hsub | exact hfin.subset hsub

theorem lw_pos (w : HeightOneSpectrum (𝓞 K)) : 0 < lw w := by
  unfold lw
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
  have h2 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
    exact_mod_cast (by omega : 1 < Ideal.absNorm w.asIdeal)
  apply div_pos (Real.log_pos h2)
  exact_mod_cast Module.finrank_pos

theorem finsum_over {g : ℕ} (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite)
    (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : PlOver g w), f w = ∑ w ∈ hS.toFinset, f w := by
  exact finsum_mem_eq_finite_toFinset_sum f hS

theorem plOver_mem {g : ℕ} (hg : 0 < g) (w : HeightOneSpectrum (𝓞 K)) (h : PlOver g w) :
    (g : 𝓞 K) ∈ w.asIdeal := by
  classical
  have hc : ((g : 𝓞 K) : K) = (g : K) := by simp
  have hg0 : (g : 𝓞 K) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold PlOver vw at h
  rw [← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ] at h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := by
    exact_mod_cast h
  have hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h1
  exact h1

end Places

section Star

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_conj_nat (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) :
    vw (conjPl w) (g : K) = vw w (g : K) := by
  rw [← ValuationRepresentative.vw_star, star_natCast]

theorem plOver_conj (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : PlOver g (conjPl w) ↔ PlOver g w := by
  unfold PlOver
  rw [vw_conj_nat]

private theorem conjPl_conjPl_lemma {K : Type} [Field K] [NumberField K] [StarRing K]
    (w : HeightOneSpectrum (𝓞 K)) : conjPl (conjPl w) = w := by
  have hinv : ∀ x : 𝓞 K, cO K (cO K x) = x := by
    intro x
    apply RingOfIntegers.ext
    first
      | (simp [cO]; done)
      | (change star (star (x : K)) = (x : K); exact star_star _)
      | (simp [cO, RingOfIntegers.mapRingEquiv]; done)
  have key : (w.asIdeal.map (cO K)).map (cO K) = w.asIdeal := by
    ext x
    simp only [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rw [hinv]; exact hz
    · intro hx
      exact ⟨cO K x, ⟨x, hx, rfl⟩, hinv x⟩
  exact HeightOneSpectrum.ext key

theorem sum_conj {g : ℕ} (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite)
    (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∑ w ∈ hS.toFinset, f (conjPl w) = ∑ w ∈ hS.toFinset, f w := by
  apply Finset.sum_nbij' conjPl conjPl
  · intro w hw
    simp only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw ⊢
    exact (plOver_conj g w).2 hw
  · intro w hw
    simp only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw ⊢
    exact (plOver_conj g w).2 hw
  · intro w _; exact conjPl_conjPl_lemma w
  · intro w _; exact conjPl_conjPl_lemma w
  · intro w _; rfl

theorem vw_pow (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0) (n : ℕ) :
    vw w (a ^ n) = (n : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

end Star

theorem sum_lw_vw (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {g : ℕ}
    (hg : 0 < g) (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite) :
    ∑ w ∈ hS.toFinset, lw w * (vw w (g : K) : ℝ) = Real.log g := by
  obtain ⟨_, h⟩ := prod_formula' K (g : K) (natCast_ne_zero' hg)
  have h1 : ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (g : K) : ℝ) =
      ∑ w ∈ hS.toFinset, lw w * (vw w (g : K) : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    rw [Function.mem_support] at hw
    have h0 : vw w (g : K) ≠ 0 := by
      intro h0
      apply hw
      rw [h0]
      simp
    have := vw_nat_nonneg (K := K) g w
    unfold PlOver
    omega
  rw [← h1, ← h]
  have hn : (finrank ℚ K : ℝ) = 2 * (Fintype.card (InfinitePlace K) : ℝ) := by
    have h2 := IsTotallyComplex.finrank (K := K)
    have h3 : InfinitePlace.nrComplexPlaces K = Fintype.card (InfinitePlace K) := by
      have := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
      rw [nrRealPlaces_eq_zero_iff.mpr inferInstance] at this
      omega
    rw [h2, h3]
    push_cast
    ring
  have hc : (0 : ℝ) < Fintype.card (InfinitePlace K) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hnorm : ∀ v : InfinitePlace K, ‖v.embedding (g : K)‖ = (g : ℝ) := by
    intro v
    rw [map_natCast]
    simp
  simp only [hnorm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hn]
  field_simp

end PlaceSumConjugation

open PlaceSumConjugation

theorem weighted_log_sum_over_places : LwSumOver := by
  unfold LwSumOver
  intro K _ _ _ _ g hg
  have hS := plOver_finite (K := K) g
  refine ⟨hS, fun w => vw_conj_nat g w, fun w => plOver_conj g w, fun w => lw_pos w, ?_⟩
  rw [finsum_over hS]
  exact sum_lw_vw K hg hS

theorem places_over_coprime : PlOverCoprime := by
  unfold PlOverCoprime
  intro K _ _ g g' hcop w ⟨h1, h2⟩
  have hpos : ∀ n : ℕ, PlOver n w → 0 < n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      unfold PlOver vw at hn
      first | simp [FractionalIdeal.count_zero] at hn | (unfold FractionalIdeal.count at hn; simp at hn)
    · exact h0
  have m1 := plOver_mem (hpos g h1) w h1
  have m2 := plOver_mem (hpos g' h2) w h2
  have hab : (Nat.gcdA g g') * (g : ℤ) + (Nat.gcdB g g') * (g' : ℤ) = 1 := by
    have := Nat.gcd_eq_gcd_ab g g'
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    push_cast at this
    linarith
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : 𝓞 K) = ((Nat.gcdA g g' : ℤ) : 𝓞 K) * (g : 𝓞 K) + ((Nat.gcdB g g' : ℤ) : 𝓞 K) * (g' : 𝓞 K) := by
    exact_mod_cast hab.symm
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m1) (Ideal.mul_mem_left _ _ m2)

theorem second_complement_normaliser : Complement2Normaliser := by
  intro K _ _ _ g hg pb hpb Psi _ p ν hp w
  have hg0 : (g : K) ≠ 0 := natCast_ne_zero' hg
  have hpb0 : pb ≠ 0 := by
    intro h
    apply hg0
    rw [← hpb, h, zero_mul]
  have hprod : ∏ τ, p τ ^ ν τ = pb ^ (∑ τ, ν τ) := by
    simp only [hp]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hprod, vw_pow w pb hpb0, vw_pow (conjPl w) pb hpb0, ← hpb,
    ValuationRepresentative.vw_mul w _ _ hpb0 (by rwa [ne_eq, star_eq_zero]), ValuationRepresentative.vw_star]
  ring

theorem second_complement_scalar : Complement2Scalar := by
  intro K _ _ _ v0 hv0 cg hcg w
  have hcg0 : cg ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hcg
    exact zero_ne_one hcg
  have h1 : cg * star cg = 1 := by
    apply v0.embedding.injective
    rw [map_mul, hv0, map_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, hcg]
    simp
  have h2 := ValuationRepresentative.vw_mul w cg (star cg) hcg0 (by rwa [ne_eq, star_eq_zero])
  rw [h1, ValuationRepresentative.vw_one, ValuationRepresentative.vw_star] at h2
  omega

private theorem lw_conjPl_lemma {K : Type} [Field K] [NumberField K] [StarRing K]
    (w : HeightOneSpectrum (𝓞 K)) : lw (conjPl w) = lw w := by
  have h : Ideal.absNorm (conjPl w).asIdeal = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv w.asIdeal (conjPl w).asIdeal (cO K) rfl).toEquiv.symm
  unfold lw
  rw [h]

theorem second_complement_arithmetic : Complement2Arith := by
  unfold Complement2Arith
  intro K _ _ _ _ g hg E F nn cg m Dpi Dp Dm er hE hF hcg hnn
  have hS := plOver_finite (K := K) g
  rw [finsum_over hS]
  have hmem : ∀ w, w ∈ hS.toFinset ↔ PlOver g w := fun w => by simp
  have hsc := sum_conj hS (fun w => lw w * E w)
  simp only [lw_conjPl_lemma] at hsc
  have hlog : ∑ w ∈ hS.toFinset, lw w * (vw w (g : K) : ℝ) = Real.log g := sum_lw_vw K hg hS
  have hpt : ∀ w ∈ hS.toFinset, |lw w * E w + lw w * E (conjPl w) -
      (Dpi - Dp - Dm) * (lw w * (vw w (g : K) : ℝ))| ≤ 2 * er * (lw w * (vw w (g : K) : ℝ)) := by
    intro w hw
    have hw' := (hmem w).1 hw
    have hwc : PlOver g (conjPl w) := (plOver_conj g w).2 hw'
    have h1 := hE w hw'
    have h2 := hE (conjPl w) hwc
    rw [hF w hw'] at h1
    rw [hF (conjPl w) hwc, vw_conj_nat g w] at h2
    have h3 : ((vw w cg : ℤ) : ℝ) + ((vw (conjPl w) cg : ℤ) : ℝ) = 0 := by exact_mod_cast hcg w hw'
    have h5 : ((vw w cg : ℤ) : ℝ) / m + ((vw (conjPl w) cg : ℤ) : ℝ) / m = 0 := by
      rw [← add_div, h3, zero_div]
    have h4 := hnn w hw'
    have hl := lw_pos w
    have key : |E w + E (conjPl w) - (Dpi - Dp - Dm) * (vw w (g : K) : ℝ)| ≤
        2 * er * (vw w (g : K) : ℝ) := by
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    calc |lw w * E w + lw w * E (conjPl w) - (Dpi - Dp - Dm) * (lw w * (vw w (g : K) : ℝ))|
        = |lw w * (E w + E (conjPl w) - (Dpi - Dp - Dm) * (vw w (g : K) : ℝ))| := by
          congr 1; ring
      _ = lw w * |E w + E (conjPl w) - (Dpi - Dp - Dm) * (vw w (g : K) : ℝ)| := by
          rw [abs_mul, abs_of_pos hl]
      _ ≤ lw w * (2 * er * (vw w (g : K) : ℝ)) := mul_le_mul_of_nonneg_left key hl.le
      _ = 2 * er * (lw w * (vw w (g : K) : ℝ)) := by ring
  have h2sum : 2 * ∑ w ∈ hS.toFinset, lw w * E w =
      ∑ w ∈ hS.toFinset, (lw w * E w + lw w * E (conjPl w)) := by
    rw [Finset.sum_add_distrib, hsc]; ring
  rw [h2sum, ← hlog, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ w ∈ hS.toFinset, |lw w * E w + lw w * E (conjPl w) -
        (Dpi - Dp - Dm) * (lw w * (vw w (g : K) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ hS.toFinset, 2 * er * (lw w * (vw w (g : K) : ℝ)) := Finset.sum_le_sum hpt

theorem sum_top {Pl : Type} [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (f : Pl → ℝ) :
    ∑ t ∈ TT, f t = ∑ ρ, if ρ ∈ TT then f ρ else 0 := by
  symm
  rw [← Finset.sum_filter]
  congr 1
  ext ρ
  simp

theorem second_complement_degree : Complement2Degree := by
  unfold Complement2Degree
  intro Pl _ TT _ aT w nν δν δpm k Dpi Dp Dm hDpi hnν hD
  have h1 : Dpi - Dp - Dm = ∑ ρ, (nν ρ - ((k - 1) * w ρ + δpm ρ)) := by
    rw [Finset.sum_sub_distrib, ← hDpi, ← hD]; ring
  rw [h1, sum_top TT aT, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  simp only [hnν ρ]
  split_ifs <;> ring

theorem second_complement_sum : Complement2Sum := by
  unfold Complement2Sum
  intro K _ _ _ _ g hg hcop E F hEfin nn cg m Dpi Dp Dm er Eels hE hF hcg hnn hEels Pl _ TT _
    aT w nν δν δpm k hDpi hnν hD
  classical
  have hdeg := second_complement_degree Pl TT aT w nν δν δpm k Dpi Dp Dm hDpi hnν hD
  have hA : ∀ i, |2 * (∑ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : PlOver (g i) v), lw v * E v) -
      (Dpi - Dp - Dm) * Real.log (g i : ℝ)| ≤ 2 * er * Real.log (g i : ℝ) := fun i =>
    second_complement_arithmetic K (g i) (hg i) E F (nn i) (cg i) m Dpi Dp Dm er (hE i) (hF i) (hcg i)
      (hnn i)
  have hdisj : ∀ v, ¬ (PlOver (g 0) v ∧ PlOver (g 1) v) := fun v =>
    places_over_coprime K (g 0) (g 1) hcop v
  have hsupp : (Function.support fun v : HeightOneSpectrum (𝓞 K) => lw v * E v).Finite :=
    hEfin.subset (fun v hv => by
      rw [Function.mem_support] at hv ⊢; intro h; exact hv (by rw [h, mul_zero]))
  have hsub : ∀ (P : HeightOneSpectrum (𝓞 K) → Prop),
      (Function.support fun v => ∑ᶠ (_ : P v), lw v * E v).Finite := fun P =>
    hsupp.subset (fun v hv => by
      rw [Function.mem_support] at hv ⊢; intro h; apply hv; rw [h]; simp)
  have hsplit : ∀ v : HeightOneSpectrum (𝓞 K), lw v * E v =
      ((∑ᶠ (_ : PlOver (g 0) v), lw v * E v) + ∑ᶠ (_ : PlOver (g 1) v), lw v * E v) +
      ∑ᶠ (_ : ∀ i, ¬ PlOver (g i) v), lw v * E v := by
    intro v
    have hd := hdisj v
    simp only [finsum_eq_if]
    by_cases h0 : PlOver (g 0) v <;> by_cases h1 : PlOver (g 1) v
    · exact absurd ⟨h0, h1⟩ hd
    · have hn : ¬ ∀ i, ¬ PlOver (g i) v := fun h => h 0 h0
      rw [if_pos h0, if_neg h1, if_neg hn]; ring
    · have hn : ¬ ∀ i, ¬ PlOver (g i) v := fun h => h 1 h1
      rw [if_neg h0, if_pos h1, if_neg hn]; ring
    · have hn : ∀ i, ¬ PlOver (g i) v := Fin.forall_fin_two.mpr ⟨h0, h1⟩
      rw [if_neg h0, if_neg h1, if_pos hn]; ring
  have hsum3 : ∑ᶠ v, lw v * E v =
      ((∑ᶠ (v) (_ : PlOver (g 0) v), lw v * E v) + ∑ᶠ (v) (_ : PlOver (g 1) v), lw v * E v) +
      ∑ᶠ (v) (_ : ∀ i, ¬ PlOver (g i) v), lw v * E v := by
    rw [finsum_congr hsplit, finsum_add_distrib, finsum_add_distrib]
    all_goals first
      | exact hsub _
      | exact ((hsub _).union (hsub _)).subset (Function.support_add _ _)
  have hO : |∑ᶠ (v) (_ : ∀ i, ¬ PlOver (g i) v), lw v * E v| ≤ Eels := by
    refine le_trans ?_ hEels
    have hs1 : (Function.support fun v => ∑ᶠ (_ : ∀ i, ¬ PlOver (g i) v), lw v * E v) ⊆
        hsupp.toFinset := by
      intro v hv
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      rw [Function.mem_support] at hv
      intro h; apply hv; rw [h]; simp
    have hs2 : (Function.support fun v => ∑ᶠ (_ : ∀ i, ¬ PlOver (g i) v), lw v * |E v|) ⊆
        hsupp.toFinset := by
      intro v hv
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      rw [Function.mem_support] at hv
      intro h; apply hv
      have hl := lw_pos v
      have hE0 : E v = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hl.ne'
        · exact h'
      rw [hE0]; simp
    rw [finsum_eq_sum_of_support_subset _ hs1, finsum_eq_sum_of_support_subset _ hs2]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun v _ => ?_))
    have hl := lw_pos v
    by_cases hq : ∀ i, ¬ PlOver (g i) v
    · simp only [finsum_eq_if, if_pos hq, abs_mul, abs_of_pos hl, le_refl]
    · simp only [finsum_eq_if, if_neg hq, abs_zero, le_refl]
  have hAB : |(∑ ρ, if ρ ∈ TT then 0 else w ρ) + ∑ ρ, (δν ρ - δpm ρ)| ≤
      (∑ ρ, if ρ ∈ TT then 0 else |w ρ|) + ∑ ρ, (|δν ρ| + |δpm ρ|) := by
    have h1 : |∑ ρ, (if ρ ∈ TT then 0 else w ρ)| ≤ ∑ ρ, (if ρ ∈ TT then 0 else |w ρ|) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum (fun ρ _ => by split_ifs <;> simp))
    have h2 : |∑ ρ, (δν ρ - δpm ρ)| ≤ ∑ ρ, (|δν ρ| + |δpm ρ|) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun ρ _ => by
        rw [abs_le]; constructor <;> linarith [le_abs_self (δν ρ), neg_abs_le (δν ρ),
          le_abs_self (δpm ρ), neg_abs_le (δpm ρ)]))
    rw [abs_le] at h1 h2 ⊢; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hL0 : 0 ≤ Real.log (g 0 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hg 0).ne')
  have hL1 : 0 ≤ Real.log (g 1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hg 1).ne')
  have hlog : Real.log ((g 0 : ℝ) * (g 1 : ℝ)) = Real.log (g 0 : ℝ) + Real.log (g 1 : ℝ) :=
    Real.log_mul (Nat.cast_ne_zero.mpr (hg 0).ne') (Nat.cast_ne_zero.mpr (hg 1).ne')
  have hLg0 : 0 ≤ Real.log ((g 0 : ℝ) * (g 1 : ℝ)) := by rw [hlog]; linarith
  have hXl : |((∑ ρ, if ρ ∈ TT then 0 else w ρ) + ∑ ρ, (δν ρ - δpm ρ)) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤
      ((∑ ρ, if ρ ∈ TT then 0 else |w ρ|) + ∑ ρ, (|δν ρ| + |δpm ρ|)) * Real.log ((g 0 : ℝ) * (g 1 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hLg0]; exact mul_le_mul_of_nonneg_right hAB hLg0
  have hA0 := hA 0
  have hA1 := hA 1
  rw [hdeg] at hA0 hA1
  rw [hsum3]
  rw [hlog] at hXl ⊢
  rw [abs_le] at hA0 hA1 hO hXl ⊢
  constructor <;> linarith [hA0.1, hA0.2, hA1.1, hA1.2, hO.1, hO.2, hXl.1, hXl.2]

theorem second_complement_parameter_bounds (f m b L B0 : ℝ) (hB0 : B0 = f * m * b * L) (hf : 1 ≤ f) (hm : 1 ≤ m) (hL : 1 ≤ L)
    (hb : 0 ≤ b) : 0 ≤ f * b ∧ f * b * L ≤ B0 ∧ b ≤ B0 := by
  subst hB0
  have hf0 : 0 ≤ f := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  refine ⟨hfb, ?_, ?_⟩
  · have := mul_nonneg (mul_nonneg hfb hL0) (sub_nonneg.2 hm)
    linarith
  · have h1 : 1 ≤ f * m * L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hm) hL
    have := mul_nonneg hb (sub_nonneg.2 h1)
    linarith

theorem eta_weight_bounds (m tt η w'' : ℝ) (hm : 1 ≤ m) (htt : 0 ≤ tt) (hη : 0 ≤ η)
    (h : m * (tt + 1) * η ≤ w'') : m * η ≤ w'' ∧ m * tt * η ≤ w'' := by
  have hm0 : 0 ≤ m := by linarith
  have h1 : 0 ≤ m * η := mul_nonneg hm0 hη
  have h2 : 0 ≤ m * tt * η := mul_nonneg (mul_nonneg hm0 htt) hη
  constructor <;> linarith

theorem second_complement_error_bound (C0 f N tt m η b w'' er : ℝ) (hC0 : 0 ≤ C0) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hNN : N * (N + tt) ≤ b) (hmη : m * η ≤ w'') (hwb : w'' ≤ b)
    (her : er ≤ C0 * (f * (N * (N + tt) + m ^ 2 * η))) : er ≤ C0 * (f * (b + m * b)) := by
  have hm0 : 0 ≤ m := by linarith
  have hmb : m * η ≤ b := le_trans hmη hwb
  have h1 : m * (m * η) ≤ m * b := mul_le_mul_of_nonneg_left hmb hm0
  have h2 : f * (N * (N + tt) + m ^ 2 * η) ≤ f * (b + m * b) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 hC0
  linarith

theorem second_complement_els_bound (C0 B0 f b L k b' N X'' logd c Eels : ℝ) (hC0 : 0 ≤ C0) (hf : 1 ≤ f) (hb : 0 ≤ b)
    (hk : 1 ≤ k) (hb' : 0 ≤ b') (hc : c ≤ f) (hkb : k * b' ≤ b)
    (hX : f * k * N * X'' ≤ b) (hd0 : 0 ≤ logd) (hd : logd ≤ L) (hfbL : f * b * L ≤ B0)
    (hbB0 : b ≤ B0)
    (hE : Eels ≤ C0 * B0 + (c * (2 * b + 4 * k * b') + 4 * f * k * b') * logd +
      C0 * (f * k * N * X'')) : Eels ≤ (2 * C0 + 10) * B0 := by
  have hf0 : 0 ≤ f := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hkb0 : 0 ≤ k * b' := mul_nonneg hk0 hb'
  have hpos : 0 ≤ 2 * b + 4 * k * b' := by linarith
  have e1 : c * (2 * b + 4 * k * b') ≤ f * (2 * b + 4 * k * b') :=
    mul_le_mul_of_nonneg_right hc hpos
  have e2 : f * (k * b') ≤ f * b := mul_le_mul_of_nonneg_left hkb hf0
  have hcoef : c * (2 * b + 4 * k * b') + 4 * f * k * b' ≤ 10 * (f * b) := by linarith
  have e3 : (c * (2 * b + 4 * k * b') + 4 * f * k * b') * logd ≤ 10 * (f * b) * logd :=
    mul_le_mul_of_nonneg_right hcoef hd0
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  have e4 : f * b * logd ≤ f * b * L := mul_le_mul_of_nonneg_left hd hfb
  have e5 : C0 * (f * k * N * X'') ≤ C0 * B0 :=
    mul_le_mul_of_nonneg_left (le_trans hX hbB0) hC0
  linarith

theorem second_complement_absorption (W' Dl er lg Eels C0 f m b L B0 : ℝ) (hB0 : B0 = f * m * b * L) (hf : 1 ≤ f)
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hC0 : 0 ≤ C0) (hfbL : f * b * L ≤ B0)
    (hW : W' ≤ f * (2 * b)) (hDl : Dl ≤ f * (5 * C0 * b)) (her : er ≤ C0 * (f * (b + m * b)))
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ C0 * L) (hE : Eels ≤ (2 * C0 + 10) * B0) :
    (W' + Dl + 2 * er) * lg + 2 * Eels ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0 := by
  subst hB0
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  have hfmb : 0 ≤ f * m * b := mul_nonneg (mul_nonneg hf0 hm0) hb
  have hS : W' + Dl + 2 * er ≤ f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b) := by linarith
  have hU0 : 0 ≤ f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b) :=
    add_nonneg (mul_nonneg hfb (by linarith)) (mul_nonneg (by linarith) hfmb)
  have h1 : (W' + Dl + 2 * er) * lg ≤ (f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b)) * lg :=
    mul_le_mul_of_nonneg_right hS hlg0
  have h2 : (f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b)) * lg ≤
      (f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b)) * (C0 * L) :=
    mul_le_mul_of_nonneg_left hlg hU0
  have h3 : C0 * (2 + 7 * C0) * (f * b * L) ≤ C0 * (2 + 7 * C0) * (f * m * b * L) :=
    mul_le_mul_of_nonneg_left hfbL (mul_nonneg hC0 (by linarith))
  linarith

theorem second_complement_delta_bound (C0 k S m tt η b w'' z dν dpm : ℝ) (hC0 : 0 ≤ C0) (hkS : k * S ≤ w'')
    (h1 : m * η ≤ w'') (h2 : m * tt * η ≤ w'') (hwb : w'' ≤ b) (hz : z ≤ b)
    (hν : dν ≤ C0 * (k * S + m * tt * η + z)) (hpm : dpm ≤ C0 * (k * S + m * η)) :
    dν + dpm ≤ 5 * C0 * b := by
  have g1 : C0 * (k * S + m * tt * η + z) ≤ C0 * (3 * b) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  have g2 : C0 * (k * S + m * η) ≤ C0 * (2 * b) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  linarith

theorem second_complement : Complement2 := by
  unfold Complement2
  intro K _ _ _ _ g hg hcop J Pl _ _ TT _ E F hEfin nn cg Dpi Dp Dm er Eels aT w nν δν δpm
    x eps L b B0 m f k N S tt η w'' b' X'' logd C0 hE hF hcg hnn hEels hDpi hnν hD hx heps hL hb
    hB0 hJ hPl hm hf hk hN hS htt hη hb' hlogd hwb hkS hmη hNw hNN hkb hX hdL hlg hC0 her hδν
    hδpm hEe
  have hL1 : 1 ≤ L := by rw [hL]; exact Real.one_le_rpow hx heps.le
  have hB0' : B0 = f * m * b * L := by rw [hB0, hL]
  obtain ⟨hfb0, hfbL, hbB0⟩ := second_complement_parameter_bounds f m b L B0 hB0' hf hm hL1 hb
  have hη1 := eta_weight_bounds m tt η w'' hm htt hη hmη
  have hw0 : 0 ≤ w'' := le_trans (mul_nonneg (by linarith) hS) hkS
  have hw'' : w'' ≤ b := by have := mul_nonneg hw0 (sub_nonneg.2 hN); linarith
  have hg0 : (1 : ℝ) ≤ (g 0 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hg 0).ne'
  have hg1 : (1 : ℝ) ≤ (g 1 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hg 1).ne'
  have hlg0 : 0 ≤ Real.log ((g 0 : ℝ) * (g 1 : ℝ)) := Real.log_nonneg (by nlinarith)
  have hcf : (TT.card : ℝ) ≤ f := le_trans (by exact_mod_cast Finset.card_le_univ TT) hPl
  have hone : ∀ j, |2 * (∑ᶠ v : HeightOneSpectrum (𝓞 K), lw v * E j v) - (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0 := by
    intro j
    have hs := second_complement_sum K g hg hcop (E j) (F j) (hEfin j) (nn j) cg m (Dpi j) (Dp j)
      (Dm j) (er j) (Eels j) (hE j) (hF j) hcg (hnn j) (hEels j) Pl TT aT (w j) (nν j) (δν j)
      (δpm j) k (hDpi j) (hnν j) (hD j)
    refine le_trans hs ?_
    refine second_complement_absorption _ _ _ _ _ C0 f m b L B0 hB0' hf hm hb hC0 hfbL ?_ ?_ ?_ hlg0 hlg ?_
    · calc ∑ ρ, (if ρ ∈ TT then 0 else |w j ρ|) ≤ ∑ _ρ : Pl, 2 * b := by
            apply Finset.sum_le_sum
            intro ρ _
            obtain ⟨h1, h2⟩ := hwb j ρ
            split_ifs
            · linarith
            · rw [abs_of_nonneg h1]; exact h2
        _ = (Fintype.card Pl : ℝ) * (2 * b) := by simp
        _ ≤ f * (2 * b) := mul_le_mul_of_nonneg_right hPl (by linarith)
    · calc ∑ ρ, (|δν j ρ| + |δpm j ρ|) ≤ ∑ _ρ : Pl, 5 * C0 * b := by
            apply Finset.sum_le_sum
            intro ρ _
            have hz : (if ρ ∈ TT then b' / x else 0) ≤ b := by
              split_ifs
              · have h1 : b' / x ≤ b' := div_le_self hb' hx
                have h2 : b' ≤ k * b' := by
                  have := mul_nonneg hb' (sub_nonneg.2 hk); linarith
                linarith
              · exact hb
            exact second_complement_delta_bound C0 k S m tt η b w'' _ _ _ hC0 hkS hη1.1 hη1.2 hw'' hz (hδν j ρ) (hδpm j ρ)
        _ = (Fintype.card Pl : ℝ) * (5 * C0 * b) := by simp
        _ ≤ f * (5 * C0 * b) :=
            mul_le_mul_of_nonneg_right hPl (mul_nonneg (mul_nonneg (by norm_num) hC0) hb)
    · exact second_complement_error_bound C0 f N tt m η b w'' (er j) hC0 hf hm hNN hη1.1 hw'' (her j)
    · exact second_complement_els_bound C0 B0 f b L k b' N X'' logd (TT.card : ℝ) (Eels j) hC0 hf hb hk hb' hcf hkb hX
        hlogd hdL hfbL hbB0 (hEe j)
  refine ⟨hone, ?_⟩
  have e : 2 * (∑ j, (∑ᶠ v : HeightOneSpectrum (𝓞 K), lw v * E j v)) - m * ((∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))) = ∑ j, (2 * (∑ᶠ v : HeightOneSpectrum (𝓞 K), lw v * E j v) - (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hJ, Finset.mul_sum]
  rw [e]
  calc _ ≤ ∑ j, |2 * (∑ᶠ v : HeightOneSpectrum (𝓞 K), lw v * E j v) - (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J, (9 * C0 ^ 2 + 6 * C0 + 20) * B0 := Finset.sum_le_sum (fun j _ => hone j)
    _ = (9 * C0 ^ 2 + 6 * C0 + 20) * (m * B0) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hJ]; ring

theorem phi_difference_le_mul_log (y y' : ℝ) (h1 : 1 ≤ y') (h : y' ≤ y) :
    0 ≤ Formalism.LatticeIndexTer.ph y - Formalism.LatticeIndexTer.ph y' ∧ Formalism.LatticeIndexTer.ph y - Formalism.LatticeIndexTer.ph y' ≤ (y - y') * Real.log y := by
  have hy'0 : 0 < y' := by linarith
  have hy0 : 0 < y := by linarith
  have hy'ne : y' ≠ 0 := hy'0.ne'
  have hyne : y ≠ 0 := hy0.ne'
  simp only [Formalism.LatticeIndexTer.ph]
  have hl1 : Real.log y - Real.log y' ≤ y / y' - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hy'0)
    rwa [Real.log_div hyne hy'ne] at this
  have hl2 : Real.log y' - Real.log y ≤ y' / y - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hy'0 hy0)
    rwa [Real.log_div hy'ne hyne] at this
  have e1 : y' * (y / y') = y := by first | (field_simp; done) | (field_simp; ring) | (rw [mul_div_assoc']; exact mul_div_cancel_left₀ y hy'ne)
  have e2 : y * (y' / y) = y' := by first | (field_simp; done) | (field_simp; ring) | (rw [mul_div_assoc']; exact mul_div_cancel_left₀ y' hyne)
  have hly' : 0 ≤ Real.log y' := Real.log_nonneg h1
  have k1 := mul_le_mul_of_nonneg_left hl1 hy'0.le
  have k2 := mul_le_mul_of_nonneg_left hl2 hy0.le
  have k3 : 0 ≤ (y - y') * Real.log y' := mul_nonneg (by linarith) hly'
  constructor
  · linarith
  · linarith

theorem phi_lipschitz_bound : PhLip := by
  unfold PhLip
  intro y y' A hy hy' hyA hy'A
  have key : ∀ a a' : ℝ, 1 ≤ a' → a' ≤ a → a ≤ A →
      |Formalism.LatticeIndexTer.ph a - Formalism.LatticeIndexTer.ph a'| ≤ |a - a'| * Real.log A := by
    intro a a' ha' haa' haA
    obtain ⟨h0, h1⟩ := phi_difference_le_mul_log a a' ha' haa'
    have hlog : Real.log a ≤ Real.log A := Real.log_le_log (by linarith) haA
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - a')]
    calc Formalism.LatticeIndexTer.ph a - Formalism.LatticeIndexTer.ph a' ≤ (a - a') * Real.log a := h1
      _ ≤ (a - a') * Real.log A := mul_le_mul_of_nonneg_left hlog (by linarith)
  rcases le_total y' y with h | h
  · exact key y y' hy' h hyA
  · rw [abs_sub_comm, abs_sub_comm y y']
    exact key y' y hy h hy'A

private theorem phpair_lemma (u u' A La lo D : ℝ) (hu : 1 ≤ u) (hu' : 1 ≤ u') (hA : u ≤ A)
    (hA' : u' ≤ A) (hLa : La = Real.log A) (hLa0 : 0 ≤ La) (hlo : |lo| ≤ La)
    (hD : |u - u'| ≤ D) :
    |(Formalism.LatticeIndexTer.ph u - u * lo) - (Formalism.LatticeIndexTer.ph u' - u' * lo)| ≤ 2 * (D * La) := by
  have hP := phi_lipschitz_bound u u' A hu hu' hA hA'
  rw [← hLa] at hP
  have hY : |(u - u') * lo| ≤ |u - u'| * La := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlo (abs_nonneg _)
  have hDL : |u - u'| * La ≤ D * La := mul_le_mul_of_nonneg_right hD hLa0
  rw [abs_le] at hP hY ⊢
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨hY1, hY2⟩ := hY
  constructor <;> linarith

theorem phi_sum_difference_cluster (n : ℕ) (w Sc A La lo : ℝ) (c c' : Fin n → ℝ) (hw : 1 ≤ w) (hA : w + Sc ≤ A)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ Sc) (hc' : ∀ i, 0 ≤ c' i ∧ c' i ≤ Sc) (hLa : La = Real.log A)
    (hLa0 : 0 ≤ La) (hlo : |lo| ≤ La) :
    |(∑ i, Formalism.LatticeIndexTer.ph (w + c i) - (∑ i, (w + c i)) * lo) -
      (∑ i, Formalism.LatticeIndexTer.ph (w + c' i) - (∑ i, (w + c' i)) * lo)| ≤ 2 * ((n : ℝ) * Sc * La) := by
  have hterm : ∀ i, |(Formalism.LatticeIndexTer.ph (w + c i) - (w + c i) * lo) -
      (Formalism.LatticeIndexTer.ph (w + c' i) - (w + c' i) * lo)| ≤ 2 * (Sc * La) := by
    intro i
    apply phpair_lemma (w + c i) (w + c' i) A La lo Sc (by linarith [(hc i).1])
      (by linarith [(hc' i).1]) (by linarith [(hc i).2]) (by linarith [(hc' i).2]) hLa hLa0 hlo
    rw [show w + c i - (w + c' i) = c i - c' i by ring, abs_le]
    constructor <;> linarith [(hc i).1, (hc i).2, (hc' i).1, (hc' i).2]
  calc |(∑ i, Formalism.LatticeIndexTer.ph (w + c i) - (∑ i, (w + c i)) * lo) -
        (∑ i, Formalism.LatticeIndexTer.ph (w + c' i) - (∑ i, (w + c' i)) * lo)|
      = |∑ i, ((Formalism.LatticeIndexTer.ph (w + c i) - (w + c i) * lo) -
        (Formalism.LatticeIndexTer.ph (w + c' i) - (w + c' i) * lo))| := by
        congr 1; simp only [Finset.sum_sub_distrib, Finset.sum_mul]
    _ ≤ ∑ i, |(Formalism.LatticeIndexTer.ph (w + c i) - (w + c i) * lo) -
        (Formalism.LatticeIndexTer.ph (w + c' i) - (w + c' i) * lo)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, 2 * (Sc * La) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 2 * ((n : ℝ) * Sc * La) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem phi_difference_near_endpoint (w a Δ A La lo y y' : ℝ) (hw : 1 ≤ w) (ha : 0 ≤ a) (hy : a ≤ y ∧ y ≤ a + Δ)
    (hy' : a ≤ y' ∧ y' ≤ a + Δ) (hA : y + w ≤ A) (hA' : y' + w ≤ A) (hLa : La = Real.log A)
    (hLa0 : 0 ≤ La) (hlo : |lo| ≤ La) :
    |(Formalism.LatticeIndexTer.ph (y + w) - (y + w) * lo) - (Formalism.LatticeIndexTer.ph (y' + w) - (y' + w) * lo)| ≤
      2 * (Δ * La) := by
  have hD : |y + w - (y' + w)| ≤ Δ := by
    rw [show y + w - (y' + w) = y - y' by ring, abs_le]
    constructor <;> linarith [hy.1, hy.2, hy'.1, hy'.2]
  exact phpair_lemma (y + w) (y' + w) A La lo Δ (by linarith [hy.1]) (by linarith [hy'.1])
    hA hA' hLa hLa0 hlo hD

theorem third_complement_final_bound (C0 c a La m B0 f b L S Sc η N k w'' b' Δ tt P1 P1' MM TTm cPl : ℝ)
    (hB0 : B0 = f * m * b * L) (hf : 1 ≤ f) (hm : 1 ≤ m) (hL1 : 1 ≤ L) (hb : 0 ≤ b)
    (hc0 : 0 ≤ c) (ha : 0 ≤ a) (hLLa : L ≤ La) (hLa3 : La ≤ 3 * L) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hS : 0 ≤ S) (hSc : Sc ≤ 3 * S) (htt : 0 ≤ tt) (hη : 0 ≤ η) (hb' : 0 ≤ b')
    (hcPl0 : 0 ≤ cPl) (hcPl : cPl ≤ f)
    (h3 : m ^ 3 * N ^ 2 * L ≤ b) (hkN : k * N ≤ b) (hkS : k * S ≤ w'')
    (hmη : m * (tt + 1) * η ≤ w'') (hNw : N * w'' ≤ b) (hmkb : m * k * b' ≤ a) (hmΔ : m * Δ ≤ a)
    (hP1 : |P1| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L))
    (hP1' : |P1'| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L))
    (hMM : |MM| ≤ m * (cPl * (2 * (k * Sc * La)) + c * (2 * (Δ * La))))
    (hT : |TTm| ≤ m * (C0 * (f * m ^ 2 * N ^ 2)) * (C0 * m * L)) :
    |P1 - P1' + MM + TTm| ≤ (7 * C0 ^ 2 + 18) * (c * a * La + m * B0) := by
  subst hB0
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLa0 : 0 ≤ La := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hkS0 : 0 ≤ k * S := mul_nonneg hk0 hS
  have hw0 : 0 ≤ w'' := le_trans hkS0 hkS
  have hw1 : w'' ≤ b := by
    have := mul_nonneg hw0 (sub_nonneg.2 hN); linarith
  have hS1 : S ≤ w'' := by
    have := mul_nonneg hS (sub_nonneg.2 hk); linarith
  have hmη1 : m * η ≤ w'' := by
    have := mul_nonneg (mul_nonneg hm0 htt) hη; linarith
  have hN1 : N ≤ b := by
    have := mul_nonneg hN0 (sub_nonneg.2 hk); linarith
  have hmη0 : 0 ≤ m * η := mul_nonneg hm0 hη
  have hsum : S + m * η + N ≤ 3 * b := by linarith
  have hmb' : m * b' ≤ a := by
    have := mul_nonneg (mul_nonneg hm0 hb') (sub_nonneg.2 hk); linarith
  have hc1 : c * (m * b') ≤ c * a := mul_le_mul_of_nonneg_left hmb' hc0
  have hc2 : cPl * (S + m * η + N) ≤ f * (3 * b) :=
    le_trans (mul_le_mul_of_nonneg_left hsum hcPl0)
      (mul_le_mul_of_nonneg_right hcPl (by linarith))
  have hca : 0 ≤ c * a := mul_nonneg hc0 ha
  have hcaL : c * a * L ≤ c * a * La := mul_le_mul_of_nonneg_left hLLa hca
  have hmLX : m * L * (c * b' + cPl * (S + m * η + N)) ≤ c * a * La + 3 * (f * m * b * L) := by
    have g1 := mul_le_mul_of_nonneg_left hc1 hL0
    have g2 := mul_le_mul_of_nonneg_left hc2 (mul_nonneg hm0 hL0)
    linarith
  have hP1b : |P1| ≤ C0 ^ 2 * (c * a * La + 3 * (f * m * b * L)) :=
    calc |P1| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L) := hP1
      _ = C0 ^ 2 * (m * L * (c * b' + cPl * (S + m * η + N))) := by ring
      _ ≤ C0 ^ 2 * (c * a * La + 3 * (f * m * b * L)) :=
        mul_le_mul_of_nonneg_left hmLX (sq_nonneg C0)
  have hP1'b : |P1'| ≤ C0 ^ 2 * (c * a * La + 3 * (f * m * b * L)) :=
    calc |P1'| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L) := hP1'
      _ = C0 ^ 2 * (m * L * (c * b' + cPl * (S + m * η + N))) := by ring
      _ ≤ C0 ^ 2 * (c * a * La + 3 * (f * m * b * L)) :=
        mul_le_mul_of_nonneg_left hmLX (sq_nonneg C0)
  have t1 : cPl * (k * Sc * La) ≤ f * (k * (3 * S) * La) := by
    have a1 : k * Sc * La ≤ k * (3 * S) * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSc hk0) hLa0
    have a2 : 0 ≤ k * (3 * S) * La := mul_nonneg (mul_nonneg hk0 (by linarith)) hLa0
    exact le_trans (mul_le_mul_of_nonneg_left a1 hcPl0) (mul_le_mul_of_nonneg_right hcPl a2)
  have t2 : k * S * La ≤ b * (3 * L) := mul_le_mul (le_trans hkS hw1) hLa3 hLa0 hb
  have t3 : m * f * (k * S * La) ≤ m * f * (b * (3 * L)) :=
    mul_le_mul_of_nonneg_left t2 (mul_nonneg hm0 hf0)
  have t4 : m * Δ * (c * La) ≤ a * (c * La) :=
    mul_le_mul_of_nonneg_right hmΔ (mul_nonneg hc0 hLa0)
  have t5 : m * (cPl * (k * Sc * La)) ≤ m * (f * (k * (3 * S) * La)) :=
    mul_le_mul_of_nonneg_left t1 hm0
  have hMMb : |MM| ≤ 2 * (c * a * La) + 18 * (f * m * b * L) := by
    rw [abs_le] at hMM ⊢
    constructor <;> linarith [hMM.1, hMM.2]
  have hTb : |TTm| ≤ C0 ^ 2 * (f * m * b * L) := by
    have u1 : f * m * (m ^ 3 * N ^ 2 * L) ≤ f * m * b :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hf0 hm0)
    have u2 : f * m * b ≤ f * m * b * L := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hf0 hm0) hb) (sub_nonneg.2 hL1); linarith
    calc |TTm| ≤ m * (C0 * (f * m ^ 2 * N ^ 2)) * (C0 * m * L) := hT
      _ = C0 ^ 2 * (f * m * (m ^ 3 * N ^ 2 * L)) := by ring
      _ ≤ C0 ^ 2 * (f * m * b * L) := mul_le_mul_of_nonneg_left (le_trans u1 u2) (sq_nonneg C0)
  have hB0' : 0 ≤ f * m * b * L := mul_nonneg (mul_nonneg (mul_nonneg hf0 hm0) hb) hL0
  have hcaLa : 0 ≤ c * a * La := mul_nonneg hca hLa0
  have q1 : 0 ≤ C0 ^ 2 * (c * a * La) := mul_nonneg (sq_nonneg C0) hcaLa
  have q2 : 0 ≤ (f * m * b * L) * (m - 1) := mul_nonneg hB0' (by linarith)
  have q3 : 0 ≤ C0 ^ 2 * ((f * m * b * L) * (m - 1)) := mul_nonneg (sq_nonneg C0) q2
  rw [abs_le] at hP1b hP1'b hMMb hTb ⊢
  constructor <;> linarith [hP1b.1, hP1b.2, hP1'b.1, hP1'b.2, hMMb.1, hMMb.2, hTb.1, hTb.2]

theorem third_complement : Complement3 := by
  unfold Complement3
  intro U J Pl _ _ TT _ n hu hP logT hK aT nτ phν nν c mlam logκ cP cT e6 logOm logg cK w fa pr nr
    x eps L b a rd La B0 m f k N S Sc tt η w'' b' Δ C0 Hhu HhP HhK Hmlam Hphν Hnν Hc HSc0 HSc Hnk
    HaT HmΔ Hw HaTw HlogT HcT0 HcT Hnτ Hx Heps HL Hb Ha Hrd Hlogrd Hlogx HLa HB0 HJ HPl Hm Hf Hk
    HN HS Htt Hη Hb' hermFormPi_zeroTorus HlogOm H3 HkN HkS Hmη HNw Hmkb u u'
  have hm0 : 0 ≤ m := by linarith
  have hL1 : 1 ≤ L := by rw [HL]; exact Real.one_le_rpow Hx Heps.le
  have hb0 : 0 < b := by rw [Hb]; exact Real.exp_pos L
  have hx0 : 0 < x := by linarith
  have hapos : 0 < a := by rw [Ha]; exact mul_pos hx0 hb0
  have ha0 : 0 ≤ a := hapos.le
  have hLa_eq : La = Real.log x + L + Real.log rd := by
    rw [HLa, Real.log_mul hapos.ne' (by linarith : (0 : ℝ) < rd).ne', Ha,
      Real.log_mul hx0.ne' hb0.ne', Hb, Real.log_exp]
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg Hx
  have hlrd0 : 0 ≤ Real.log rd := Real.log_nonneg Hrd
  have hLLa : L ≤ La := by rw [hLa_eq]; linarith
  have hLa3 : La ≤ 3 * L := by rw [hLa_eq]; linarith
  have hLa0 : 0 ≤ La := by linarith
  have hB0' : B0 = f * m * b * L := by rw [HB0, HL]
  have hsT : ∑ ρ : Pl, (if ρ ∈ TT then b' else 0) = (TT.card : ℝ) * b' := by
    rw [← sum_top]; simp
  have hsT2 : ∑ ρ : Pl, (if ρ ∈ TT then 2 * (Δ * La) else 0) = (TT.card : ℝ) * (2 * (Δ * La)) := by
    rw [← sum_top]; simp
  have hX : 0 ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) := by
    apply mul_nonneg hermFormPi_zeroTorus
    apply add_nonneg (mul_nonneg (Nat.cast_nonneg _) Hb')
    apply mul_nonneg (Nat.cast_nonneg _)
    have := mul_nonneg hm0 Hη
    linarith
  have hP1gen : ∀ v, |((∑ ρ, (if ρ ∈ TT then aT v ρ else 0)) - ∑ ρ, nτ v ρ) * logT v| ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) * (C0 * m * L) := by
    intro v
    obtain ⟨hl0, hl1⟩ := HlogT v
    have hsum : |∑ ρ, (nτ v ρ - (if ρ ∈ TT then aT v ρ else 0))| ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) := by
      calc _ ≤ ∑ ρ, |nτ v ρ - (if ρ ∈ TT then aT v ρ else 0)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ ρ, C0 * ((if ρ ∈ TT then b' else 0) + S + m * η + N) :=
            Finset.sum_le_sum (fun ρ _ => Hnτ v ρ)
        _ = C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_congr rfl (fun ρ _ => (show (if ρ ∈ TT then b' else 0) + S + m * η + N =
              (if ρ ∈ TT then b' else 0) + (S + m * η + N) by ring)), Finset.sum_add_distrib, hsT]
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have e : ((∑ ρ, (if ρ ∈ TT then aT v ρ else 0)) - ∑ ρ, nτ v ρ) * logT v = -(∑ ρ, (nτ v ρ - (if ρ ∈ TT then aT v ρ else 0))) * logT v := by
      rw [Finset.sum_sub_distrib]; ring
    rw [e, abs_mul, abs_neg, abs_of_nonneg hl0]
    calc _ ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) * logT v := mul_le_mul_of_nonneg_right hsum hl0
      _ ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) * (C0 * m * L) := mul_le_mul_of_nonneg_left hl1 hX
  have hterm : ∀ j ρ, |(phν u j ρ - nν u j ρ * logOm) - (phν u' j ρ - nν u' j ρ * logOm)| ≤
      2 * (k * Sc * La) + (if ρ ∈ TT then 2 * (Δ * La) else 0) := by
    intro j ρ
    rw [Hphν u j ρ, Hphν u' j ρ, Hnν u j ρ, Hnν u' j ρ]
    obtain ⟨hw1, hwA⟩ := Hw j ρ
    have hcl := phi_sum_difference_cluster n (w j ρ) Sc (a * rd) La logOm (c u j ρ) (c u' j ρ) hw1 hwA
      (fun i => Hc u j ρ i) (fun i => Hc u' j ρ i) HLa hLa0 HlogOm
    have hnk : (n : ℝ) * (Sc * La) ≤ k * (Sc * La) :=
      mul_le_mul_of_nonneg_right Hnk (mul_nonneg HSc0 hLa0)
    rw [abs_le] at hcl
    split_ifs with hρ
    · obtain ⟨ha1, ha2⟩ := HaT u ρ hρ
      obtain ⟨hb1, hb2⟩ := HaT u' ρ hρ
      have htop := phi_difference_near_endpoint (w j ρ) a Δ (a * rd) La logOm (aT u ρ) (aT u' ρ) hw1 ha0 ⟨ha1, ha2⟩
        ⟨hb1, hb2⟩ (HaTw u j ρ hρ) (HaTw u' j ρ hρ) HLa hLa0 HlogOm
      rw [abs_le] at htop ⊢
      constructor <;> linarith [hcl.1, hcl.2, htop.1, htop.2]
    · rw [abs_le]
      constructor <;> linarith [hcl.1, hcl.2]
  have hMM : |∑ j, ∑ ρ, ((phν u j ρ - nν u j ρ * logOm) - (phν u' j ρ - nν u' j ρ * logOm))| ≤
      m * ((Fintype.card Pl : ℝ) * (2 * (k * Sc * La)) + (TT.card : ℝ) * (2 * (Δ * La))) := by
    calc _ ≤ ∑ j, |∑ ρ, ((phν u j ρ - nν u j ρ * logOm) - (phν u' j ρ - nν u' j ρ * logOm))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : J, ∑ ρ : Pl, (2 * (k * Sc * La) + (if ρ ∈ TT then 2 * (Δ * La) else 0)) :=
          Finset.sum_le_sum (fun j _ => le_trans (Finset.abs_sum_le_sum_abs _ _)
            (Finset.sum_le_sum (fun ρ _ => hterm j ρ)))
      _ = m * ((Fintype.card Pl : ℝ) * (2 * (k * Sc * La)) + (TT.card : ℝ) * (2 * (Δ * La))) := by
          simp only [Finset.sum_add_distrib, hsT2, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, HJ] <;> ring
  have hT : |m * cT * (logT u - logT u')| ≤ m * (C0 * (f * m ^ 2 * N ^ 2)) * (C0 * m * L) := by
    obtain ⟨a0, a1⟩ := HlogT u
    obtain ⟨b0, b1⟩ := HlogT u'
    have hd : |logT u - logT u'| ≤ C0 * m * L := by
      rw [abs_le]; constructor <;> linarith
    have hmc : 0 ≤ m * cT := mul_nonneg hm0 HcT0
    rw [abs_mul, abs_of_nonneg hmc]
    calc m * cT * |logT u - logT u'| ≤ m * cT * (C0 * m * L) := mul_le_mul_of_nonneg_left hd hmc
      _ ≤ m * (C0 * (f * m ^ 2 * N ^ 2)) * (C0 * m * L) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left HcT hm0
  have hid : (hu u + ∑ t ∈ TT, aT u t * logT u) - (hu u' + ∑ t ∈ TT, aT u' t * logT u') =
      ((∑ ρ, (if ρ ∈ TT then aT u ρ else 0)) - ∑ ρ, nτ u ρ) * logT u - ((∑ ρ, (if ρ ∈ TT then aT u' ρ else 0)) - ∑ ρ, nτ u' ρ) * logT u' + ∑ j, ∑ ρ, ((phν u j ρ - nν u j ρ * logOm) - (phν u' j ρ - nν u' j ρ * logOm)) + m * cT * (logT u - logT u') := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_top TT (aT u), sum_top TT (aT u'), Hhu u, Hhu u',
      HhP u, HhP u']
    simp only [HhK, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, HJ] <;> ring
  rw [hid]
  exact third_complement_final_bound C0 (TT.card : ℝ) a La m B0 f b L S Sc η N k w'' b' Δ tt _ _ _ _
    (Fintype.card Pl : ℝ) hB0' Hf Hm hL1 hb0.le (Nat.cast_nonneg _) ha0 hLLa hLa3 Hk HN HS HSc Htt Hη
    Hb' (Nat.cast_nonneg _) HPl H3 HkN HkS Hmη HNw Hmkb HmΔ (hP1gen u) (hP1gen u') hMM hT

end Formalism.DivisionValues
