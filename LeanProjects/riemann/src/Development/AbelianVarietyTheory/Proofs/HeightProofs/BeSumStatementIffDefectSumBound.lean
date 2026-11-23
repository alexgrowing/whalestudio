import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

open NumberField IsDedekindDomain Pointwise Formalism.L2.Pj.QAt GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.DefectSumCompare

theorem pow_finrank_eq_span_absNorm {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hfix : ∀ σ : E ≃ₐ[ℚ] E, σ • I = I) :
    I ^ Module.finrank ℚ E = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} := by
  classical
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have hprin : (I ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨x, hx⟩ := hprin
  have hx' : I ^ h = Ideal.span {x} := hx
  have hσ : ∀ σ : E ≃ₐ[ℚ] E, Ideal.span {σ • x} = I ^ h := by
    intro σ
    have : σ • (I ^ h) = I ^ h := by rw [smul_pow', hfix]
    rw [← this, hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 E) = ∏ σ : E ≃ₐ[ℚ] E, σ • x := by
    apply RingOfIntegers.ext
    have h1 := Algebra.norm_eq_prod_automorphisms ℚ (x : E)
    rw [← Algebra.coe_norm_int] at h1
    change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [map_prod, map_intCast]
    rw [map_intCast] at h1
    exact h1
  have h2 : Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} ^ h = (I ^ Module.finrank ℚ E) ^ h := by
    rw [Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]
    have h3 : Ideal.span {(((Algebra.norm ℤ x).natAbs : ℕ) : 𝓞 E)} =
        Ideal.span {((Algebra.norm ℤ x : ℤ) : 𝓞 E)} := by
      rcases Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4
      · conv_rhs => rw [h4]
        rw [Int.cast_natCast]
      · conv_rhs => rw [h4]
        rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
    rw [h3, hnorm, ← Ideal.prod_span_singleton]
    simp only [hσ]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      ← pow_mul, ← pow_mul, mul_comm]
  exact (pow_left_injective hpos h2).symm

theorem ord_vw_eq_vla {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : ord_vw la I = vla la I := by
  classical
  unfold ord_vw vla
  rw [Ideal.count_associates_factors_eq hI la.isPrime la.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI]

theorem lrd_eq_lrdOf (E : Type) [Field E] [NumberField E] : lrd E = lrdOf E := by
  unfold lrd lrdOf
  rw [rootDiscr_def, one_div, Int.cast_abs]

theorem log_discr_eq (E : Type) [Field E] [NumberField E] :
    Real.log |((discr E : ℤ) : ℝ)| = (Module.finrank ℚ E : ℝ) * lrd E := by
  have hd : (0 : ℝ) < |((discr E : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [lrd_eq_lrdOf]
  unfold lrdOf
  rw [Real.log_rpow hd]
  field_simp

theorem conjDifferent_pow {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ^ Module.finrank ℚ E = discAt E K := by
  unfold conjDifferent discAt
  rw [← Ideal.map_pow, pow_finrank_eq_span_absNorm _ differentIdeal_ne_bot
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.smul_differentIdeal, absNorm_differentIdeal E, Ideal.map_span,
    Set.image_singleton, map_natCast]

theorem vla_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (k : ℕ) : vla la (I ^ k) = k * vla la I := by
  unfold vla
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr hI) la.associates_irreducible]

section Galois

variable {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]

theorem vla_discAt (σ : E →+* K) (la : HeightOneSpectrum (𝓞 K)) :
    vla la (discAt E K) = Module.finrank ℚ E * ord_vw la (conjDifferent σ) := by
  rw [← conjDifferent_pow σ, vla_pow la (conjDifferent_ne_bot σ), ord_vw_eq_vla la (conjDifferent_ne_bot σ)]

theorem finrank_mul_defectAt (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    (Module.finrank ℚ E : ℝ) * defectAt_vw σ n' a la =
      beOf E ((n' : ℕ) ^ Module.finrank ℚ E) a la := by
  have h : mOf E ((n' : ℕ) ^ Module.finrank ℚ E) la = Module.finrank ℚ E *
      max (ord_vw la (conjDifferent σ)) (ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)})) := by
    unfold mOf
    rw [vla_discAt σ, Nat.cast_pow, ← Ideal.span_singleton_pow, vla_pow la (span_natCast_ne_bot n'),
      ord_vw_eq_vla la (span_natCast_ne_bot n'), Nat.mul_max_mul_left]
  unfold beOf defectAt_vw
  rw [h]
  push_cast
  ring

theorem defect_vw_eq_defectAt (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    defect_vw E n' a la = defectAt_vw σ n' a la := by
  refine le_antisymm (Finset.sup_le fun τ _ => le_of_eq ?_) (defectAt_vw_le σ n' a la)
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have := (finrank_mul_defectAt τ n' a la).trans (finrank_mul_defectAt σ n' a la).symm
  exact_mod_cast mul_left_cancel₀ hn this

theorem finrank_mul_defect (hσ : Nonempty (E →+* K)) (n' : ℕ+) (a : ℕ)
    (la : HeightOneSpectrum (𝓞 K)) :
    (Module.finrank ℚ E : ℝ) * defect_vw E n' a la =
      beOf E ((n' : ℕ) ^ Module.finrank ℚ E) a la := by
  obtain ⟨σ⟩ := hσ
  rw [defect_vw_eq_defectAt σ, finrank_mul_defectAt]

theorem support_eq (hσ : Nonempty (E →+* K)) (n' : ℕ+) (a : ℕ) :
    Function.support (defect_vw E (K := K) n' a) =
      Function.support (beOf E (K := K) ((n' : ℕ) ^ Module.finrank ℚ E) a) := by
  ext la
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp only [Function.mem_support, ← finrank_mul_defect hσ, ne_eq, mul_eq_zero, hn, false_or,
    Nat.cast_eq_zero]

end Galois

end GlobalTheory.DefectSumCompare
