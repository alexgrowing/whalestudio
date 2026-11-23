import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamSt
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.MorseGenSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionBasisLocalUniformBound

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem berg_le_uniform {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) :
    ∃ C : ℝ, ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis x n b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ pts (coordIdeal ℤ x),
        bergmanDensity μ (fun k => secFun (b k)) (wgt (interp m₀ m₁ t) n) z ≤ C * (n : ℝ) ^ D := by
  classical
  obtain ⟨N, U, C, γ, hγ, hC, hcov⟩ := exists_finite_param_cover hg₀
  choose M hM0 hM using fun a => section_basis_local_uniform_bound hg₀ hg₁ (hγ a) (hC a).1 (hC a).2
  refine ⟨∑ a, M a, ?_⟩
  intro n r b hn hb t ht z hz
  have hgt := isGood_interp hg₀ hg₁ ht
  obtain ⟨a, y₀, hy₀, e, he, rfl⟩ := hcov z hz
  have hMa : M a ≤ ∑ a, M a := Finset.single_le_sum (fun a _ => hM0 a) (Finset.mem_univ a)
  have hS0 : 0 ≤ ∑ a, M a := Finset.sum_nonneg fun a _ => hM0 a
  refine berg_le_of_forall μ _ _ (fun z => cone_metric_weight_nonneg _ _ z) (fun i j => integrable_secFun hgt hb i j)
    (posDef_bGram_secFun hgt hb) _ _ (mul_nonneg hS0 (pow_nonneg (Nat.cast_nonneg _) _)) fun c => ?_
  have hdeg := isDegreeZero_weightedCombination (interp m₀ m₁ t) hb.1 c e (γ a y₀) he
  simp only at hdeg ⊢
  rw [hdeg]
  calc _ ≤ M a * (n : ℝ) ^ D * bNormSq μ (fun k => secFun (b k)) (wgt (interp m₀ m₁ t) n) c :=
        hM a n r b hn hb t ht y₀ hy₀ c
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMa (pow_nonneg (Nat.cast_nonneg _) _)) (sectionNormSq_nonneg _ _ _ _)

theorem sup_le_l2_norm_sections {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) :
    ∃ C : ℝ, ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis x n b →
      ∀ (c : Fin r → ℂ), ∀ z ∈ pts (coordIdeal ℤ x),
        ‖∑ k, c k * secFun (b k) z‖ ^ 2 * wgt m n z ≤
          C * (n : ℝ) ^ D * bNormSq μ (fun k => secFun (b k)) (wgt m n) c := by
  obtain ⟨C, hC⟩ := berg_le_uniform hg hg
  refine ⟨C, fun n r b hn hb c z hz => ?_⟩
  have hw : wgt (interp m m 0) n = wgt m n := by
    funext z; simp [wgt, interp]
  have h := hC n r b hn hb 0 ⟨le_rfl, zero_le_one⟩ z hz
  rw [hw] at h
  calc _ ≤ bergmanDensity μ (fun k => secFun (b k)) (wgt m n) z * bNormSq μ (fun k => secFun (b k)) (wgt m n) c :=
        sq_le_berg_mul μ _ _ (fun z => cone_metric_weight_nonneg _ _ z) (fun i j => integrable_secFun hg hb i j)
          (posDef_bGram_secFun hg hb) c z
    _ ≤ _ := mul_le_mul_of_nonneg_right h (sectionNormSq_nonneg _ _ _ _)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
