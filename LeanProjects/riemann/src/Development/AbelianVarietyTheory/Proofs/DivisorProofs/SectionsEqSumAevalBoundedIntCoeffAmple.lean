import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusAmpleSectionIsAffineModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldBasisOfSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsCoeffLeOfHomogeneousTorusBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralQuotientRingSectionTupleLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIntTraceSectionTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAevalTraceFormLeFibreValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSRep

open MvPolynomial

theorem aeval_smul_of_hom {σ K : Type} [CommRing K] {d : ℕ} {P : MvPolynomial σ ℤ} (hP : P.IsHomogeneous d)
    (c : K) (y : σ → K) : aeval (c • y) P = c ^ d * aeval y P := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hP (mem_support_iff.1 ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

theorem rep_of_trace {K : Type} [Field K] [CharZero K] {D : ℕ} (x : Fin (D + 1) → K) (hx0 : x 0 ≠ 0)
    [FiniteDimensional (ratF x) K] (g : Fin (Module.finrank (ratF x) K) → K) (hg : LinearIndependent (ratF x) g) :
    ∃ w : Fin (Module.finrank (ratF x) K) → K, ∀ (N : ℕ) (f : K)
      (T : Fin (Module.finrank (ratF x) K) → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous N) →
      (∀ i, (Algebra.trace (ratF x) K (f * g i / x 0 ^ N) : K) = aeval (fun l => x l / x 0) (T i)) →
      f = ∑ i, aeval x (T i) * w i := by
  classical
  haveI : Nonempty (Fin (Module.finrank (ratF x) K)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hg (by simp)
  have hB : (Algebra.traceForm (ratF x) K).Nondegenerate := traceForm_nondegenerate _ _
  refine ⟨fun i => (Algebra.traceForm (ratF x) K).dualBasis hB b i, ?_⟩
  intro N f T hT htr
  have key := ((Algebra.traceForm (ratF x) K).dualBasis hB b).sum_repr (f / x 0 ^ N)
  simp_rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at key
  have hxN : x 0 ^ N ≠ 0 := pow_ne_zero _ hx0
  have hf : f = (f / x 0 ^ N) * x 0 ^ N := by field_simp
  rw [hf, ← key, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hbi : b i = g i := by simp [b]
  have hx : x = x 0 • fun l => x l / x 0 := by
    funext l; simp [smul_eq_mul, mul_div_cancel₀ _ hx0]
  rw [Algebra.smul_def, hbi, div_mul_eq_mul_div, show (algebraMap (ratF x) K) (Algebra.trace (ratF x) K (f * g i / x 0 ^ N)) = _ from htr i]
  have hT' : aeval x (T i) = x 0 ^ N * aeval (fun l => x l / x 0) (T i) := by
    conv_lhs => rw [hx]
    exact aeval_smul_of_hom (hT i) _ _
  rw [hT']
  ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f := by
  rw [← norm_val]; exact norm_nonneg _

theorem sections_eq_sum_aeval_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (w : Fin (Module.finrank (ratF x) X.functionField) → X.functionField) (C : ℝ), 0 < C ∧ ∀ (q : ℕ), ∀ f ∈ P.H (e * q + a) b, ∃ T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i ∧ ∀ R κ : ℝ, 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (e * q + a) b σ y f ≤ R) → ∀ i α, |((MvPolynomial.coeff α (T i) : ℤ) : ℝ)| ≤ C * R / κ ^ (q + c) := by
  intro k _ X _ p D hV P hA e x hG a b
  classical
  obtain ⟨hx0s, hai, hfd⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hV P hA e x hG
  haveI := hfd
  obtain ⟨hch, -⟩ := GlobalTheory.T.projArith_functionField_charZero_trdeg k X p D hV
  haveI := hch
  set n' := Module.finrank (ratF x) X.functionField with hn'
  obtain ⟨c0, g0, hg0, hli0⟩ := GlobalTheory.T.exists_functionField_basis_of_sections k X p D hV P hA e x hG (-a) (-b)

  have hli : LinearIndependent (ratF x) (fun i => g0 i * x 0) := by
    have hk : LinearMap.ker (LinearMap.mulRight (ratF x) (x 0)) = ⊥ :=
      LinearMap.ker_eq_bot.2 (mul_left_injective₀ (hx0s 0))
    have := hli0.map' (LinearMap.mulRight (ratF x) (x 0)) hk
    exact this
  have hgH : ∀ i, (fun j => g0 j * x 0) i ∈ P.H (e * c0 + -a + e) (-b + 0) := fun i =>
    (NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ (hg0 i) (hG.mem 0)).1
  generalize hgdef : (fun j => g0 j * x 0) = g at hli hgH
  obtain ⟨w, hw⟩ := rep_of_trace x (hx0s 0) g hli

  have hbd : ∀ i, ∃ Ci : ℝ, ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) ≤ Ci :=
    fun i => ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hV P _ _).2 _ (hgH i)).2
  choose Ci hCi using hbd
  set Cg : ℝ := ∑ i, |Ci i| + 1 with hCg
  have hCg1 : 1 ≤ Cg := by
    have : 0 ≤ ∑ i, |Ci i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hCgi : ∀ i σ y, P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) ≤ Cg := fun i σ y => by
    have h1 : Ci i ≤ |Ci i| := le_abs_self _
    have h2 : |Ci i| ≤ ∑ j, |Ci j| := Finset.single_le_sum (f := fun j => |Ci j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [hCi i σ y]
  have hn'pos : (0 : ℝ) < n' := by exact_mod_cast Module.finrank_pos
  refine ⟨c0 + 1, w, n' * Cg, by positivity, ?_⟩
  intro q f hf
  set N := q + (c0 + 1) with hNdef
  have hN1 : 1 ≤ N := by omega
  have hidx : ((e : ℤ) * q + a) + (e * c0 + -a + e) = (N : ℤ) * e := by rw [hNdef]; push_cast; ring
  have hidx2 : b + (-b + 0) = (N : ℤ) * 0 := by ring
  have hu : ∀ i, f * g i ∈ P.H ((N : ℤ) * e) ((N : ℤ) * 0) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      P.nu ((N : ℤ) * e) ((N : ℤ) * 0) σ y (f * g i) =
        P.nu (e * q + a) b σ y f * P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) := fun i => by
    have := NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ f (g i) hf (hgH i)
    rw [hidx, hidx2] at this
    exact this
  have hxpow : ∀ l, x l ^ N ∈ P.H ((N : ℤ) * e) ((N : ℤ) * 0) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      P.nu ((N : ℤ) * e) ((N : ℤ) * 0) σ y (x l ^ N) = P.nu e 0 σ y (x l) ^ N := fun l =>
    NuPow.pow_mem_H_and_nu_pow k X p P _ _ (x l) (hG.mem l) N
  have hnv : ∀ l, NV P ((N : ℤ) * e) ((N : ℤ) * 0) (x l ^ N) = NV P e 0 (x l) := fun l =>
    (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hG.mem l)).2.2.1 N hN1
  have hreg : ∀ i l, ∀ z ∈ NV P e 0 (x l), RegAt z (f * g i / x l ^ N) := fun i l z hz =>
    ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P _ _ (x l ^ N) (hxpow l).1).2.2.2.1 _ (hu i).1 z (by rw [hnv l]; exact hz)).1
  have hintg : ∀ i l, IsIntegral (ratR x l) (f * g i / x l ^ N) := fun i l =>
    GlobalTheory.T.isIntegral_quotientRing_sectionTuple_locus k X p D hV P e x hG l _ (hx0s l) (hreg i l)
  have hTex : ∀ i, ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous N ∧
      (Algebra.trace (ratF x) X.functionField (f * g i / x 0 ^ N) : X.functionField) = aeval (fun l => x l / x 0) T :=
    fun i => GlobalTheory.T.exists_homogeneous_int_trace_sectionTuple X.functionField D x hx0s hai hfd N (f * g i) (hintg i)
  choose T hT htr using hTex
  refine ⟨T, hT, hw N f T hT htr, ?_⟩
  intro R κ hκ hcov hR i α
  obtain ⟨U, hgen, hU, -, hregU, -, -, hpts⟩ := GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model k X p D hV P hA e (x 0) hG.pos (hG.mem 0) (hx0s 0)
  have hB : ∀ l, x l / x 0 ∈ (fnOf U hgen).range := fun l => (hregU _).1 fun z hz =>
    ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x 0) (hG.mem 0)).2.2.2.1 _ (hG.mem l) z (by rw [← hU]; exact hz)).1
  have hBint : ∀ b' ∈ (fnOf U hgen).range, IsIntegral (ratR x 0) b' := fun b' hb =>
    GlobalTheory.T.isIntegral_quotientRing_sectionTuple_locus k X p D hV P e x hG 0 b' (hx0s 0) fun z hz => (hregU b').2 hb z (show z ∈ (U : Set X) by rw [hU]; exact hz)
  have hwB : f * g i / x 0 ^ N ∈ (fnOf U hgen).range := (hregU _).1 fun z hz => hreg i 0 z (by rw [← hU]; exact hz)
  have key := GlobalTheory.T.norm_aeval_traceForm_le_fibreValues X.functionField D x hx0s hai hfd (fnOf U hgen).range hB hBint ⟨_, hwB⟩ (T i) (htr i)
  have hcoef := GlobalTheory.T.abs_coeff_le_of_homogeneous_torus_bound D N (T i) (n' * (R * Cg / κ ^ N)) (hT i) ?_ α
  · exact le_of_le_of_eq hcoef (by ring)
  intro z hz0 hz1
  refine key z _ hz0 fun φ hφ => ?_
  obtain ⟨σ, y, hyU, hval⟩ := hpts φ
  have hyNV : under y ∈ NV P e 0 (x 0) := by rw [← hU]; exact hyU
  obtain ⟨l, hl⟩ := hcov σ y
  have h5 := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x 0) (hG.mem 0)).2.2.2.2 (x l) (hG.mem l) σ y hyNV
  have hzl : ‖ratVal (x l / x 0) y‖ = 1 := by
    have := hval ⟨_, hB l⟩
    simp only at this
    rw [this, hφ l, hz1 l]
  have hx0κ : κ ≤ P.nu e 0 σ y (x 0) := by rw [h5.1, hzl, one_mul] at hl; exact hl
  have hyN : under y ∈ NV P ((N : ℤ) * e) ((N : ℤ) * 0) (x 0 ^ N) := by rw [hnv 0]; exact hyNV
  have h6 := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P _ _ (x 0 ^ N) (hxpow 0).1).2.2.2.2 (f * g i) (hu i).1 σ y hyN
  rw [(hu i).2, (hxpow 0).2] at h6
  have hv := hval ⟨_, hwB⟩
  simp only at hv
  rw [← hv, le_div_iff₀ (pow_pos hκ N)]
  calc ‖ratVal (f * g i / x 0 ^ N) y‖ * κ ^ N ≤ ‖ratVal (f * g i / x 0 ^ N) y‖ * P.nu e 0 σ y (x 0) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ.le hx0κ N) (norm_nonneg _)
    _ = P.nu (e * q + a) b σ y f * P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) := h6.1.symm
    _ ≤ R * Cg := mul_le_mul (hR σ y) (hCgi i σ y) (nu_nonneg _ _ _ _ _ _) (le_trans (nu_nonneg _ _ _ _ _ _) (hR σ y))

end GlobalTheory.HSRep
