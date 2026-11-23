import Formalism.ThetaLogCoordinates.FockResolutionOnto.ShiftLastLetterThresholds
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem intPol_iff_norm (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by
  classical
  have hrange : x ∈ IntPol p σ ↔ x ∈ Set.range (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p])) := by
    rw [IntPol, LinearMap.mem_range, Set.mem_range]
    rfl
  rw [hrange, MvPolynomial.mem_range_map_iff_coeffs_subset]
  constructor
  · intro h m
    by_cases hm : x.coeff m = 0
    · rw [hm, norm_zero]
      exact zero_le_one
    · obtain ⟨c, hc⟩ := h (MvPolynomial.coeff_mem_coeffs m hm)
      rw [← hc]
      exact c.2
  · intro h c hc
    obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact ⟨⟨x.coeff m, h m⟩, rfl⟩

noncomputable def resL (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] where
  toFun := initPart v e
  map_add' x y := by
    ext m; simp only [coeff_initPart, coeff_add]; split_ifs <;> simp
  map_smul' a x := by
    ext m
    simp only [coeff_initPart, RingHom.id_apply, coeff_smul]
    split_ifs <;> simp

theorem resL_apply (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) : resL p v e f = initPart v e f := rfl

theorem initPart_add (v : σ) (e : ℕ) (f g : MvPolynomial σ ℚ_[p]) :
    initPart v e (f + g) = initPart v e f + initPart v e g := by
  ext m
  simp only [coeff_initPart, coeff_add]
  split_ifs <;> simp

theorem initPart_smul (v : σ) (e : ℕ) (c : ℚ_[p]) (f : MvPolynomial σ ℚ_[p]) :
    initPart v e (c • f) = c • initPart v e f := by
  ext m
  simp only [coeff_initPart, coeff_smul]
  split_ifs <;> simp

theorem initPart_int (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) (hf : f ∈ IntPol p σ) :
    initPart v e f ∈ IntPol p σ := by
  rw [intPol_iff_norm] at hf ⊢
  intro m
  rw [coeff_initPart]
  split_ifs
  · exact hf m
  · rw [norm_zero]
    exact zero_le_one

theorem initPart_zero_X_mul (v : σ) (a : MvPolynomial σ ℚ_[p]) : initPart v 0 (X v * a) = 0 := by
  classical
  ext m
  rw [coeff_initPart, coeff_zero]
  split_ifs with hm
  · rw [MvPolynomial.coeff_X_mul', if_neg (by simp [hm])]
  · rfl

theorem X_mul_int_iff (v : σ) (a : MvPolynomial σ ℚ_[p]) : X v * a ∈ IntPol p σ ↔ a ∈ IntPol p σ := by
  classical
  rw [intPol_iff_norm, intPol_iff_norm]
  constructor
  · intro h m
    have h1 := h (m + Finsupp.single v 1)
    rwa [MvPolynomial.coeff_X_mul', if_pos (by simp), add_tsub_cancel_right] at h1
  · intro h m
    rw [MvPolynomial.coeff_X_mul']
    split_ifs
    · exact h _
    · rw [norm_zero]
      exact zero_le_one

theorem smul_int (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) (a : MvPolynomial σ ℚ_[p]) (ha : a ∈ IntPol p σ) : c • a ∈ IntPol p σ := by
  rw [intPol_iff_norm] at ha ⊢
  intro m
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (ha m)

theorem norm_p_pow_le (n : ℕ) : ‖((p : ℚ_[p]) ^ n)‖ ≤ 1 := by
  have h1 : ‖(p : ℚ_[p])‖ ≤ 1 := by simpa using (p : ℤ_[p]).2
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) h1

theorem exists_div (v : σ) (h : MvPolynomial σ ℚ_[p]) :
    ∃ a, h = initPart v 0 h + X v * a ∧ (h ∈ IntPol p σ → a ∈ IntPol p σ) := by
  classical
  refine ⟨MvPolynomial.divMonomial h (Finsupp.single v 1), ?_, ?_⟩
  · have hmod : MvPolynomial.modMonomial h (Finsupp.single v 1) = initPart v 0 h := by
      ext m
      rw [coeff_initPart]
      by_cases hm : m v = 0
      · rw [if_pos hm, MvPolynomial.coeff_modMonomial_of_not_le]
        rw [Finsupp.single_le_iff]
        omega
      · rw [if_neg hm, MvPolynomial.coeff_modMonomial_of_le]
        rw [Finsupp.single_le_iff]
        omega
    have hdm := MvPolynomial.divMonomial_add_modMonomial h (Finsupp.single v 1)
    rw [← hmod]
    calc h = monomial (Finsupp.single v 1) 1 * (MvPolynomial.divMonomial h (Finsupp.single v 1)) +
          MvPolynomial.modMonomial h (Finsupp.single v 1) := hdm.symm
      _ = MvPolynomial.modMonomial h (Finsupp.single v 1) + X v * (MvPolynomial.divMonomial h (Finsupp.single v 1)) := by
        rw [add_comm]
        rfl
  · intro hh
    rw [intPol_iff_norm] at hh ⊢
    intro m
    rw [MvPolynomial.coeff_divMonomial]
    exact hh _

end Formalism.InvariantFactorPaths.L4
