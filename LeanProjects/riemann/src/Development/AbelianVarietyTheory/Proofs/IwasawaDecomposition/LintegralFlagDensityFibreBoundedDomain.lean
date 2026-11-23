import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorFlagDensityGlueLowerUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDefStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibreInt

theorem dens_neg {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : dens (-B) y = dens B y := by
  unfold dens
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_neg, Matrix.neg_mul, lminor, lminor, submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg]
  simp

theorem shear_neg_J {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (-Jpq p q) Z = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
  simp [shear, Jpq, hQ, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_neg_add]

theorem flagConst_pos (m : ℕ) : 0 < flagConst m :=
  Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity

theorem lintegral_dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  intro r p q e he A hA v hv
  set Z := toMat v with hZ
  have hH : (hQ Z).PosDef := hv
  have hd := hH.det_pos
  have hu : IsUnit (hQ Z).det := hd.ne'.isUnit
  set B : Matrix (Fin p) (Fin p) ℂ := 1 + Z * (hQ Z)⁻¹ * Zᴴ with hB
  have hBp : B.PosDef := PosDef.one.add_posSemidef (hH.inv.posSemidef.mul_mul_conjTranspose_same Z)
  have hs : schur (shear (-Jpq p q) Z) = -B := by
    rw [shear_neg_J, schur, hB]
    simp
    abel
  have h22 : (shear (-Jpq p q) Z).toBlocks₂₂ = hQ Z := by rw [shear_neg_J, toBlocks_fromBlocks₂₂]
  have hdet : B.det = ((hQ Z).det)⁻¹ := by
    have e1 : (1 : Matrix (Fin q) (Fin q) ℂ) + (hQ Z)⁻¹ * Zᴴ * Z = (hQ Z)⁻¹ := by
      rw [Matrix.mul_assoc, ← nonsing_inv_mul _ hu, ← Matrix.mul_add, hQ, sub_add_cancel, Matrix.mul_one]
    rw [hB, Matrix.mul_assoc, det_one_add_mul_comm, e1, det_nonsing_inv, Ring.inverse_eq_inv']
  obtain ⟨d, hd0, hdd⟩ : ∃ d : ℝ, 0 < d ∧ (hQ Z).det = d := by
    obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hd
    exact ⟨_, h1, Complex.ext (by simp) (by simp [← h2])⟩
  have hpt : ∀ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) =
      (ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) b.1)) * ENNReal.ofReal (dens B b.2) := by
    intro b
    rw [GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular r p q e he A (v, b) (by rw [hA]; exact h22 ▸ hu), hA]
    simp only [← hZ]
    rw [h22, hs, dens_neg, hdd, Complex.norm_real, Real.norm_of_nonneg hd0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (dens_nonneg _ _)),
      mul_comm (dens (hQ Z) b.1)]
  simp only [hpt]
  rw [Measure.volume_eq_prod, lintegral_prod_mul
    (f := fun y => ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) y))
    (g := fun y => ENNReal.ofReal (dens B y))
    ((measurable_dens _).ennreal_ofReal.const_mul _).aemeasurable (measurable_dens _).ennreal_ofReal.aemeasurable,
    lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hH, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hBp, hdet, hdd,
    ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re]
  have hp := flagConst_pos p
  have hq := flagConst_pos q
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [_root_.inv_zpow', ← mul_div_assoc _ _ (flagConst q), div_mul_div_comm, ← zpow_add₀ hd0.ne', ← zpow_add₀ hd0.ne', mul_comm (flagConst q)]
  congr 2
  push_cast
  ring

end GlobalTheory.FlagFibreInt
