import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

namespace GlobalTheory.DualEigenSum

theorem inv_eq_of_mul {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (h : Fintype.card m = Fintype.card n) (E : Matrix m m ℂ) (Zb : Matrix m n ℂ)
    (A : Matrix n n ℂ) (Zt : Matrix n m ℂ) (hE : E * (Zb * A * Zt) = 1) :
    A⁻¹ = Zt * E * Zb := by
  have h1 : (E * Zb * A) * Zt = 1 := by
    rw [← hE]; simp only [Matrix.mul_assoc]
  have h2 : Zt * (E * Zb * A) = 1 := (Matrix.mul_eq_one_comm_of_card_eq m n ℂ h).1 h1
  apply Matrix.inv_eq_left_inv
  rw [← h2]; simp only [Matrix.mul_assoc]

theorem form_dualGram_eq_sum : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∑ i, m i = g → ∀ (z : ∀ i, Fin (m i) → Fin g → ℂ) (G : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ), (∀ i, (G i).PosDef) → (∀ i b b', G i b b' = (Real.pi : ℂ) * hermForm Hm (z i b') (z i b)) → (∀ i i' b b', i ≠ i' → hermForm Hm (z i b) (z i' b') = 0) → ∀ c c' : Fin g → ℂ, HermFrame.form (HermFrame.dualGram ((Real.pi : ℂ) • Hm)) c c' = ∑ i, HermFrame.form (G i)⁻¹ (fun b => ∑ a, z i b a * c a) (fun b => ∑ a, z i b a * c' a) := by
  intro ι _ _ m g Hm _ hcard z G hG hGz horth c c'
  let Z : Matrix (Σ i, Fin (m i)) (Fin g) ℂ := Matrix.of fun p a => z p.1 p.2 a
  let Zb : Matrix (Σ i, Fin (m i)) (Fin g) ℂ := Matrix.of fun p a => star (z p.1 p.2 a)
  let A : Matrix (Fin g) (Fin g) ℂ := ((Real.pi : ℂ) • Hm).transpose
  have hc : Fintype.card (Σ i, Fin (m i)) = Fintype.card (Fin g) := by
    simp [Fintype.card_sigma, hcard]
  have hent : ∀ p q : (Σ i, Fin (m i)), (Zb * A * Z.transpose) p q
      = (Real.pi : ℂ) * hermForm Hm (z q.1 q.2) (z p.1 p.2) := by
    intro p q
    simp only [Z, Zb, A, hermForm, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.smul_apply, dotProduct, Matrix.mulVec, Pi.star_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hD : Zb * A * Z.transpose = Matrix.blockDiagonal' G := by
    ext ⟨i, b⟩ ⟨i', b'⟩
    rw [hent]
    by_cases h : i = i'
    · subst h
      rw [Matrix.blockDiagonal'_apply_eq, hGz]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, horth i' i b' b (Ne.symm h), mul_zero]
  have hE : Matrix.blockDiagonal' (fun i => (G i)⁻¹) * (Zb * A * Z.transpose) = 1 := by
    rw [hD, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
    congr 1
    funext i
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hG i).isUnit)
  have hA := inv_eq_of_mul hc _ _ _ _ hE
  have hdual : HermFrame.dualGram ((Real.pi : ℂ) • Hm)
      = Z.transpose * Matrix.blockDiagonal' (fun i => (G i)⁻¹) * Zb := by
    rw [← hA, HermFrame.dualGram, Matrix.transpose_nonsing_inv]
  have hZb : Zb.mulVec (star c') = fun p => star (∑ a, z p.1 p.2 a * c' a) := by
    funext p
    simp [Zb, Matrix.mulVec, dotProduct]
  rw [hdual, HermFrame.form, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hZb]
  simp only [HermFrame.form]
  rw [dotProduct, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fintype.sum_sigma,
    Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Matrix.blockDiagonal'_apply_eq]
    rfl
  · intro j _ hj
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

end GlobalTheory.DualEigenSum
