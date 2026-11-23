import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.blockDiagonal_eq_leviEmbedding :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (x : GL (Fin r) R) (y : GL (Fin s) R), UpperTheory.V.Af.Fin.blk x y = lev R r s (x, y) := by
  intro R _ r s x y
  have hs : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv := by
    ext (x | x) <;> simp
  have hne : ∀ (a : Fin r) (b : Fin s), Fin.castAdd s a ≠ Fin.natAdd r b := fun a b h => by
    have := congrArg Fin.val h
    have := a.isLt
    simp at *
    omega
  have h1 : (UpperTheory.V.Af.Fin.emb (UpperTheory.V.Af.Fin.e1 r s) x).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 1) := by
    rw [UpperTheory.V.Af.Fin.coe_emb]
    ext a b
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        have := UpperTheory.V.Af.Fin.matrixExtendByZero_apply (UpperTheory.V.Af.Fin.e1 r s) (x.val - 1) a b
        simp only [UpperTheory.V.Af.Fin.orderedCechToCatCochainsOne_apply_valueAtSubset] at this
        simp [this, Matrix.one_apply]
      | right b =>
        have := UpperTheory.V.Af.Fin.matrixExtendByZero_apply_of_outside_col (UpperTheory.V.Af.Fin.e1 r s) (x.val - 1) (Fin.castAdd s a) (j := Fin.natAdd r b) (fun k => (hne k b).symm)
        simp [this, Matrix.one_apply, hne]
    | right a =>
      have := UpperTheory.V.Af.Fin.extendByZero_apply_eq_zero_of_row_not_mem (UpperTheory.V.Af.Fin.e1 r s) (x.val - 1) (i := Fin.natAdd r a) (fun k => (hne k a).symm) b
      induction b using Fin.addCases with
      | left b => simp [this, Matrix.one_apply, (hne _ _).symm]
      | right b => simp [this, Matrix.one_apply]
  have h2 : (UpperTheory.V.Af.Fin.emb (UpperTheory.V.Af.Fin.e2 r s) y).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 y.val) := by
    rw [UpperTheory.V.Af.Fin.coe_emb]
    ext a b
    induction a using Fin.addCases with
    | right a =>
      induction b using Fin.addCases with
      | right b =>
        have := UpperTheory.V.Af.Fin.matrixExtendByZero_apply (UpperTheory.V.Af.Fin.e2 r s) (y.val - 1) a b
        simp only [UpperTheory.V.Af.Fin.alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
        simp [this, Matrix.one_apply]
      | left b =>
        have := UpperTheory.V.Af.Fin.matrixExtendByZero_apply_of_outside_col (UpperTheory.V.Af.Fin.e2 r s) (y.val - 1) (Fin.natAdd r a) (j := Fin.castAdd s b) (fun k => hne b k)
        simp [this, Matrix.one_apply, (hne _ _).symm]
    | left a =>
      have := UpperTheory.V.Af.Fin.extendByZero_apply_eq_zero_of_row_not_mem (UpperTheory.V.Af.Fin.e2 r s) (y.val - 1) (i := Fin.castAdd s a) (fun k => hne a k) b
      induction b using Fin.addCases with
      | left b => simp [this, Matrix.one_apply]
      | right b => simp [this, Matrix.one_apply, hne]
  refine Units.ext ?_
  rw [lev, GlobalTheory.SmGL.val_emb₂, hs, UpperTheory.V.Af.Fin.blk, Units.val_mul, h1, h2]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
