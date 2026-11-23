import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory

theorem det_schur_bilinear_entry (B : Type) [Fintype B] [DecidableEq B]
    (Q : Matrix (Option B) (Option B) ℂ) (z z' : B → ℂ) (q : ℂ)
    (hq : q = ∑ a, ∑ b, Option.elim a 1 z * Q a b * Option.elim b 1 z') (hq0 : q ≠ 0) :
    (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') *
      (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2).det = Q.det / q ^ (Fintype.card B + 1) := by
  classical
  let e : Option B ≃ B ⊕ Unit := Equiv.optionEquivSumPUnit B
  let R := Matrix.reindex e e Q
  have hR : R.det = Q.det := Matrix.det_reindex_self e Q
  let Pz : Matrix (B ⊕ Unit) (B ⊕ Unit) ℂ := Matrix.fromBlocks 1 0 (Matrix.of fun _ b => z b) 1
  let Pz' : Matrix (B ⊕ Unit) (B ⊕ Unit) ℂ := Matrix.fromBlocks 1 0 (Matrix.of fun _ b => z' b) 1
  have hPz : Pz.det = 1 := by simp [Pz, Matrix.det_fromBlocks_zero₁₂]
  have hPz' : Pz'.det = 1 := by simp [Pz', Matrix.det_fromBlocks_zero₁₂]
  let u : B → ℂ := fun a => ∑ c, Q (some a) c * Option.elim c 1 z'
  let v : B → ℂ := fun b => ∑ c, Option.elim c 1 z * Q c (some b)
  let D : Matrix Unit Unit ℂ := Matrix.of fun _ _ => q
  let M : Matrix (B ⊕ Unit) (B ⊕ Unit) ℂ :=
    Matrix.fromBlocks (Matrix.of fun a b => Q (some a) (some b)) (Matrix.of fun a _ => u a)
      (Matrix.of fun _ b => v b) D
  have hM : M = Pz * R * Pz'ᵀ := by
    ext i j
    rcases i with a | ⟨⟩ <;> rcases j with b | ⟨⟩ <;>
      simp [M, Pz, Pz', R, e, u, v, D, hq, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_option,
        Matrix.one_apply, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc, add_comm]
    all_goals
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdet : M.det = Q.det := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hPz, hPz', hR]; ring
  letI : Invertible D := ⟨Matrix.of fun _ _ => q⁻¹, by ext; simp [D, Matrix.mul_apply, hq0],
    by ext; simp [D, Matrix.mul_apply, hq0]⟩
  rw [Matrix.det_fromBlocks₂₂] at hdet
  have hD : D.det = q := by simp [D, Matrix.det_unique]
  rw [hD] at hdet
  have hS : (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') *
      (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2) =
      q⁻¹ • ((Matrix.of fun a b => Q (some a) (some b)) - (Matrix.of fun a (_ : Unit) => u a) * ⅟D *
        (Matrix.of fun (_ : Unit) b => v b)) := by
    ext a b
    simp [u, v, D, Matrix.mul_apply, invOf_eq_inv]
    field_simp
  rw [hS, Matrix.det_smul, ← hdet, pow_succ, inv_pow]
  field_simp

end GlobalTheory
