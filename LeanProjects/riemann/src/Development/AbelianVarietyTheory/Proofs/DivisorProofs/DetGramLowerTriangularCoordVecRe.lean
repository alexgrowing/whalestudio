import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open scoped Matrix

theorem GlobalTheory.det_gram_lowerTriangular_coordVec_re : ∀ (g m : ℕ) (f : Fin m → Fin g), Function.Injective f → ∀ (a : ℝ) (C : Fin m → Fin m → ℂ), (∀ i j : Fin m, i < j → C i j = 0) → (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))).det.re = (Real.pi * a) ^ m * ∏ i, ‖C i i‖ ^ 2 := by
  intro g m f hf a C hC
  classical
  set A : Matrix (Fin m) (Fin m) ℂ := Matrix.of C with hA
  set P : Matrix (Fin m) (Fin g) ℂ := Matrix.of fun l k => (Pi.single (f l) (1:ℂ) : Fin g → ℂ) k with hP
  have hX : ∀ i, (∑ l, C i l • Pi.single (f l) (1:ℂ)) = fun k => (A * P) i k := by
    intro i; ext k; simp [Matrix.mul_apply, hP, hA, Finset.sum_apply]
  have hPP : P * Pᴴ = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, hP, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    simp [Pi.single_apply, hf.eq_iff, eq_comm]
  have hH : ∀ u v : Fin g → ℂ, hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) u v = (a:ℂ) * (u ⬝ᵥ star v) := by
    intro u v
    rw [hermForm, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have hE : (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))) = ((Real.pi : ℂ) * a) • (A * Aᴴ)ᵀ := by
    ext i j
    rw [Matrix.of_apply, hX, hX, hH]
    have : (fun k => (A * P) j k) ⬝ᵥ star (fun k => (A * P) i k) = ((A * P) * (A * P)ᴴ) j i := by
      rw [Matrix.mul_apply]; simp only [dotProduct, Matrix.conjTranspose_apply, Pi.star_apply]
    rw [this, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]
    rw [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]; ring
  have hlow : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact hC i j hij
  rw [hE, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_lowerTriangular A hlow]
  have : (∏ i, A i i) * star (∏ i, A i i) = ((∏ i, ‖C i i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    simp [hA, Finset.prod_pow, norm_prod]
  rw [this, Fintype.card_fin]
  rw [show ((Real.pi : ℂ) * a) ^ m = (((Real.pi * a) ^ m : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul, Complex.ofReal_re]
