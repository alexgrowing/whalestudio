import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.NormSign

open NumberField.InfinitePlace

variable {K : Type} [Field K] [NumberField K]

noncomputable def snorm (x : mixedSpace K) : ℝ :=
  (∏ w, x.1 w) * ∏ w, ‖x.2 w‖ ^ 2

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
open NumberField.InfinitePlace in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.NormSign.snorm_mul {K : Type} [Field K] [NumberField K]
    (x y : NumberField.mixedEmbedding.mixedSpace K) :
    _root_.GlobalTheory.NormSign.snorm (x * y) = _root_.GlobalTheory.NormSign.snorm x * _root_.GlobalTheory.NormSign.snorm y := by
  simp only [_root_.GlobalTheory.NormSign.snorm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, mul_pow,
    Finset.prod_mul_distrib]
  ring

theorem snorm_smul (t : ℝ) (ht : 0 < t) (x : mixedSpace K) :
    ∃ c : ℝ, 0 < c ∧ snorm (t • x) = c * snorm x := by
  refine ⟨(∏ _w : {w : InfinitePlace K // IsReal w}, t) *
    ∏ _w : {w : InfinitePlace K // IsComplex w}, t ^ 2, by positivity, ?_⟩
  simp only [snorm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, _root_.norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, mul_pow, Finset.prod_mul_distrib]
  ring

theorem continuous_snorm : Continuous (snorm : mixedSpace K → ℝ) := by
  unfold snorm
  fun_prop

theorem abs_snorm (x : mixedSpace K) : |snorm x| = mixedEmbedding.norm x := by
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, snorm, abs_mul, Finset.abs_prod,
    Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, abs_of_nonneg (by positivity)]

theorem snorm_mixedEmbedding (x : K) :
    snorm (mixedEmbedding K x) = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x)
      (fun φ => φ x) fun _ => by simp [RingHom.equivRatAlgHom_apply]] at h
  rw [Complex.ofReal_ratCast, h, ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x),
    prod_eq_prod_mul_prod, snorm, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_prod]
  have key : ∀ w : InfinitePlace K, (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w)
      = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    intro w
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    conv_lhs => rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate,
      star_involutive.eq_iff]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [key, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp w.2), Finset.pair_eq_singleton,
      Finset.prod_singleton, mixedEmbedding_apply_isReal, embedding_of_isReal_apply]
  · refine Finset.prod_congr rfl fun w _ => ?_
    have hne : w.1.embedding ≠ ComplexEmbedding.conjugate w.1.embedding := by
      rw [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]
      exact not_isReal_iff_isComplex.mpr w.2
    rw [key, Finset.prod_pair hne, mixedEmbedding_apply_isComplex,
      ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq]

noncomputable def sgn (ε : ℂ) (t : ℝ) : ℂ := if 0 < t then 1 else if t < 0 then ε else 0

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
open NumberField.InfinitePlace in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.NormSign.sgn_mul {ε : ℂ} (hε : ε * ε = 1) (a b : ℝ) :
    _root_.GlobalTheory.NormSign.sgn ε (a * b) = _root_.GlobalTheory.NormSign.sgn ε a * _root_.GlobalTheory.NormSign.sgn ε b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · have h := mul_pos_of_neg_of_neg ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, ha.not_gt, hb.not_gt, hε]
    · simp [_root_.GlobalTheory.NormSign.sgn]
    · have h := mul_neg_of_neg_of_pos ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, ha.not_gt, h.not_gt]
  · simp [_root_.GlobalTheory.NormSign.sgn]
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · have h := mul_neg_of_pos_of_neg ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, hb.not_gt, h.not_gt]
    · simp [_root_.GlobalTheory.NormSign.sgn]
    · have h := mul_pos ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h]

theorem norm_sgn {ε : ℂ} (hε : ε * ε = 1) {a : ℝ} (ha : a ≠ 0) : ‖sgn ε a‖ = 1 := by
  have h : ‖ε‖ = 1 := by
    rcases mul_self_eq_one_iff.mp hε with h | h <;> simp [h]
  rcases lt_or_gt_of_ne ha with h' | h'
  · simp [sgn, h', h'.not_gt, h]
  · simp [sgn, h']

theorem exists_normSign (K : Type) [Field K] [NumberField K] (ε : ℂ) (hε : ε * ε = 1) :
    ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧
      (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧
      ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧
      (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧
      ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  have hne : ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 → snorm x ≠ 0 := fun x hx => by
    rwa [← abs_snorm, abs_ne_zero] at hx
  refine ⟨fun x => sgn ε (snorm x), fun x y => ?_, fun t x ht => ?_, fun x hx => ?_,
    fun x hx => norm_sgn hε (hne x hx), fun β hβ => ?_⟩
  · simp only [snorm_mul, sgn_mul hε]
  · obtain ⟨c, hc, h⟩ := snorm_smul t ht x
    simp only [h, sgn_mul hε]
    simp [sgn, hc]
  · refine ContDiffAt.contDiffWithinAt ?_
    refine (contDiffAt_const (c := sgn ε (snorm x))).congr_of_eventuallyEq ?_
    rcases lt_or_gt_of_ne (hne x hx) with h | h
    · filter_upwards [continuous_snorm.continuousAt.eventually (gt_mem_nhds h)] with y hy
      simp [sgn, h, hy, h.not_gt, hy.not_gt]
    · filter_upwards [continuous_snorm.continuousAt.eventually (lt_mem_nhds h)] with y hy
      simp [sgn, h, hy]
  · have h0 : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    simp only [snorm_mixedEmbedding, ← Algebra.coe_norm_int, Rat.cast_intCast, sgn,
      Int.cast_pos, Int.cast_lt_zero]
    rcases lt_or_gt_of_ne h0 with h | h
    · simp [h, h.not_gt]
    · simp [h]

end GlobalTheory.NormSign
