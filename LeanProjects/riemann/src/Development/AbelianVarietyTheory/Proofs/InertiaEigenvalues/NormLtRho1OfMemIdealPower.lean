import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem exists_map_eq_of_mem_sq_sup_pow {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (l N : ℕ) (π : A) (z u : B) (hπ : φ π = z) (hu : (l : B) = z * u) (a : A)
    (ha : a ∈ Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) :
    ∃ x y : B, φ a = (l : B) ^ 2 * x + z ^ N * y := by
  have hsub : Ideal.span {(l : B), z} ≤ Ideal.span {z} := by
    rw [Ideal.span_le]
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · rw [SetLike.mem_coe, hu]
      exact Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self z)
    · exact Ideal.mem_span_singleton_self z
  have hmap : Ideal.map φ (Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) ≤
      Ideal.span {(l : B) ^ 2, z ^ N} := by
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_pair]
    simp only [map_pow, map_natCast, hπ]
    refine sup_le (Ideal.span_mono (by simp)) ?_
    calc Ideal.span {(l : B), z} ^ N ≤ Ideal.span {z} ^ N := Ideal.pow_right_mono hsub N
      _ = Ideal.span {z ^ N} := Ideal.span_singleton_pow z N
      _ ≤ _ := Ideal.span_mono (by simp)
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp (hmap (Ideal.mem_map_of_mem φ ha))
  exact ⟨x, y, by rw [← hxy]; ring⟩

theorem norm_kap_lt_rho1_of_mem_sq_sup_pow :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (j n f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (ζ : OC l), 1 ≤ j → IsPrimitiveRoot (ζ : PadicComplex l) (l ^ j) → φ letπ = (ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ∀ a ∈ Ideal.span {((l : ℕ) : LetA ↥(OL LL) n) ^ 2} ⊔ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) n), letπ}) ^ (l ^ j), ∀ k, ‖kap o (φ a) k‖ < rho1 l := by
  intro l _ LL j n f o φ ζ hj hζ hφ a ha k
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hζn : ‖(ζ : PadicComplex l) - 1‖ =
      (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) :=
    norm_primitiveRoot_sub_one l j hj _ hζ
  have hlnorm : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := norm_natCast_prime_padicComplex l
  have hz0 : (ζ : PadicComplex l) - 1 ≠ 0 := by
    rw [← norm_pos_iff, hζn]
    positivity
  have hle : ‖(l : PadicComplex l)‖ ≤ ‖(ζ : PadicComplex l) - 1‖ := by
    rw [hlnorm, hζn, ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le hl.le
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) := one_le_pow₀ hl.le
    have h2 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) := by nlinarith
    rw [neg_div, neg_le_neg_iff, div_le_one (by linarith)]
    exact h2
  let u : OC l := ⟨(l : PadicComplex l) / ((ζ : PadicComplex l) - 1), by
    rw [mem_OC, norm_div]
    exact div_le_one_of_le₀ hle (norm_nonneg _)⟩
  have hu : ((l : ℕ) : OC l) = (ζ - 1) * u := by
    apply Subtype.ext
    push_cast
    change (l : PadicComplex l) =
      ((ζ : PadicComplex l) - 1) * ((l : PadicComplex l) / ((ζ : PadicComplex l) - 1))
    field_simp
  have huO : ((l : ℕ) : OCO LL) =
      ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * (u ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hu,
      ← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]
  obtain ⟨x, y, hxy⟩ := exists_map_eq_of_mem_sq_sup_pow φ l (l ^ j) letπ _ _ hφ huO a ha
  have e1 : ((l : ℕ) : OCO LL) ^ 2 = (((l : ℕ) : OC l) ^ 2) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_pow, map_natCast]
  have e2 : ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) ^ (l ^ j) =
      ((ζ - 1) ^ (l ^ j)) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
  rw [hxy, kap_add, e1, e2, kap_tmul_one_mul, kap_tmul_one_mul]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hlnorm]
    calc ((l : ℝ)⁻¹) ^ 2 * ‖kap o x k‖ ≤ ((l : ℝ)⁻¹) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o x k) (by positivity)
      _ = (l : ℝ) ^ (-(2 : ℝ)) := by
          rw [mul_one, inv_pow, Real.rpow_neg (by positivity)]
          norm_cast
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl]
          have h3 : -1 ≤ -(1 : ℝ) / ((l : ℝ) - 1) := by
            rw [neg_div, neg_le_neg_iff, div_le_one hq]
            linarith
          linarith
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hζn]
    calc ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * ‖kap o y k‖
        ≤ ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o y k) (by positivity)
      _ = (l : ℝ) ^ (-(l : ℝ) / ((l : ℝ) - 1)) := by
          rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1
          have hp : (0 : ℝ) < (l : ℝ) ^ (j - 1) := by positivity
          have hpow : ((l ^ j : ℕ) : ℝ) = (l : ℝ) * (l : ℝ) ^ (j - 1) := by
            rw [Nat.cast_pow, ← pow_succ']
            congr 1
            omega
          rw [hpow]
          field_simp
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl, div_lt_div_iff_of_pos_right hq]
          linarith

end GlobalTheory.Cyc.Decomp
