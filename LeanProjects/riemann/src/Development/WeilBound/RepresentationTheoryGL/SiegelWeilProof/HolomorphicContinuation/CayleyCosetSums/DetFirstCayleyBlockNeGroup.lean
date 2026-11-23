import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.VanishInv
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatB

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def nbar (t : ℝ) : M2 n := fromBlocks 1 0 ((t : ℂ) • 1) 1

theorem inG_nbar (t : ℝ) : InG (nbar (n := n) t) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem nbar_block (y : M2 n) (t : ℝ) : (y * nbar t).toBlocks₂₁ = y.toBlocks₂₁ + (t : ℂ) • y.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [nbar, Matrix.fromBlocks_multiply]

private theorem JJ_mul_JJ_eq_neg_one : JJ n * JJ n = -1 := by
  rw [JJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem det_ne_of_inG (x : M2 n) (hx : InG x) : x.det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [hx', JJ_mul_JJ_eq_neg_one, neg_neg]
  exact (Matrix.isUnit_det_of_left_inverse h).ne_zero

theorem det_first_cayley_block_ne_group (x : M2 n) (hx : InG x) : (u1 x).det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  rw [← Matrix.fromBlocks_toBlocks x] at hx'
  simp only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hx'
  simp at hx'
  obtain ⟨h1, h2, h3, h4⟩ := hx'
  have hu : u1 x = Complex.I • x.toBlocks₂₁ + x.toBlocks₂₂ := rfl
  rw [hu]
  set A := x.toBlocks₁₁
  set B := x.toBlocks₁₂
  set C := x.toBlocks₂₁
  set D := x.toBlocks₂₂
  have e1 : Aᴴ * C = Cᴴ * A := eq_of_sub_eq_zero (by rw [sub_eq_neg_add]; exact h1)
  have e2 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h2]; abel
  have e3 : Bᴴ * C = Dᴴ * A + -1 := by rw [← h3]; abel
  have e4 : Bᴴ * D = Dᴴ * B := eq_of_sub_eq_zero (by rw [sub_eq_neg_add]; exact h4)
  have key : (Complex.I • A + B)ᴴ * (Complex.I • C + D) - (Complex.I • C + D)ᴴ * (Complex.I • A + B)
      = (-2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [e1, e2, e3, e4]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  intro h0
  obtain ⟨v, hv, huv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have hs : star v ᵥ* (Complex.I • C + D)ᴴ = 0 := by
    rw [← Matrix.star_mulVec, huv, star_zero]
  have hz : star v ⬝ᵥ (((Complex.I • A + B)ᴴ * (Complex.I • C + D)
      - (Complex.I • C + D)ᴴ * (Complex.I • A + B)) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huv,
      Matrix.mulVec_zero, dotProduct_zero, Matrix.dotProduct_mulVec, hs, zero_dotProduct, sub_zero]
  rw [key, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hz
  have h2I : (-2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  open ComplexOrder in
  exact hv (dotProduct_star_self_eq_zero.1 ((mul_eq_zero.1 hz).resolve_left h2I))

end PositivityTheory.Rg.Sw.HSt.L3
