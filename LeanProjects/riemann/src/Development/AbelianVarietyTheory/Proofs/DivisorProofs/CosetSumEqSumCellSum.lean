import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.AnisoClauseOfFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentSiegelCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedHermN
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelCells

variable {D : D7} {n : ℕ}

def lastDiag (R : Type) [Zero R] [One R] (n j : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if n - j ≤ i.val then 1 else 0

def wMat (R : Type) [Ring R] (n j : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  StdUnn.blk4 (1 - lastDiag R n j) (lastDiag R n j) (-lastDiag R n j) (1 - lastDiag R n j)

theorem lastDiag_mul_self (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * lastDiag R n j = lastDiag R n j := by
  simp only [lastDiag, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem lastDiag_mul_one_sub (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * (1 - lastDiag R n j) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, lastDiag_mul_self, sub_self]

theorem one_sub_mul_lastDiag (R : Type) [Ring R] (n j : ℕ) : (1 - lastDiag R n j) * lastDiag R n j = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, lastDiag_mul_self, sub_self]

theorem adj_lastDiag {j : ℕ} : adj (lastDiag (AE D) n j) = lastDiag (AE D) n j := by
  ext i k
  simp only [adj, lastDiag, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : k = i
  · subst h; split_ifs <;> simp
  · simp [h, Ne.symm h]

theorem wMat_key {R : Type} [CommRing R] {n : ℕ} (L : Matrix (Fin n) (Fin n) R) (h : L * L = L) :
    StdUnn.blk4 (1 - L) (-L) L (1 - L) * StdUnn.blk4 0 1 (-1) 0 * StdUnn.blk4 (1 - L) L (-L) (1 - L) =
      StdUnn.blk4 0 1 (-1) 0 := by
  rw [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul]
  have h1 : (1 - L) * (1 - L) = 1 - L := by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h, sub_self, sub_zero]
  have h2 : L * (1 - L) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  have h3 : (1 - L) * L = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    add_zero, zero_add]
  congr 1
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, h2, h3, neg_zero, add_zero]
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, h, h1, h2, h3]; abel
  · rw [h1, h]; abel
  · rw [h2, h3]; simp

theorem exists_wPart (j : ℕ) : ∃ g : StdUnn.G D n, StdUnn.mat g = wMat (AE D) n j := by
  have e1 := lastDiag_mul_self (AE D) n j
  have e2 := lastDiag_mul_one_sub (AE D) n j
  have e3 := one_sub_mul_lastDiag (AE D) n j
  have e4 : (1 - lastDiag (AE D) n j) * (1 - lastDiag (AE D) n j) = 1 - lastDiag (AE D) n j := by
    rw [Matrix.sub_mul, Matrix.one_mul, e2, sub_zero]
  refine StdUnn.Model.exists_mat _ (StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
    (1 - lastDiag (AE D) n j)) ?_ ?_ ?_
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · have ha : adj (wMat (AE D) n j) = StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
        (1 - lastDiag (AE D) n j) := by
      rw [wMat, StdUnn.Model.adelicConjTranspose_blockMatrixTwoByTwoFin, adj_sub, adj_one, adj_neg, adj_lastDiag]
    rw [ha]
    exact wMat_key _ e1

variable (D n) in

def wPart (j : ℕ) : StdUnn.G D n := (exists_wPart (D := D) (n := n) j).choose

variable (D n) in

def hermJ (j : ℕ) : AddSubgroup (Mx D n n) where
  carrier := {b | adj b = b ∧ ∀ i k : Fin n, (i.val < n - j ∨ k.val < n - j) → b i k = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [adj_add, ha, hb], fun i k h => ?_⟩
    simp [ha' i k h, hb' i k h]
  zero_mem' := ⟨adj_zero, fun _ _ _ => rfl⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨by rw [adj_neg, ha], fun i k h => ?_⟩
    simp [ha' i k h]

variable (D n) in

def ratHermJ (j : ℕ) : AddSubgroup (hermJ D n j) := (ratMx D n n).addSubgroupOf (hermJ D n j)

def nPart {j : ℕ} (b : hermJ D n j) : StdUnn.G D n := GlobalTheory.ResAniso.nElt ⟨b.1, b.2.1⟩

variable (D n) in

def firstSpan (j : ℕ) : Submodule D.host.E (Fin n → D.host.E) :=
  LinearMap.ker (LinearMap.funLeft D.host.E D.host.E (Subtype.val : {i : Fin n // n - j ≤ i.val} → Fin n))

variable (D n) in

def Qpar (j : ℕ) : Subgroup (GL (Fin n) D.host.E) := Formalism.UG.stabGL (firstSpan D n j)

def mRat (a : GL (Fin n) D.host.E) : StdUnn.G D n :=
  (StdUnn.Model.exists_levi (Matrix.GeneralLinearGroup.map (incA D) a)).choose

def intwJ (j : ℕ) (db : Measure (hermJ D n j)) (f : StdUnn.G D n → ℂ) (g : StdUnn.G D n) : ℂ :=
  ∫ b, f (wPart D n j * nPart b * g) ∂db

def eisJ (j : ℕ) (db : Measure (hermJ D n j)) (f : StdUnn.G D n → ℂ) (g : StdUnn.G D n) : ℂ :=
  cosetSum (Qpar D n j) ⊤ (fun a => intwJ j db f (mRat a * g)) 1

def lowerRank (γ : StdUnn.G D n) : ℕ :=
  if h : ∃ M : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, rat M = StdUnn.mat γ then
    ((h.choose.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁).rank else 0

def cellSum (j : ℕ) (f : StdUnn.G D n → ℂ) (g : StdUnn.G D n) : ℂ :=
  ∑' q : Cosets (StdUnn.P D n) (StdUnn.GF D n),
    if lowerRank ((q.out : StdUnn.GF D n) : StdUnn.G D n) = j then term (StdUnn.P D n) (StdUnn.GF D n) f g q else 0

end GlobalTheory.SiegelCells

end
