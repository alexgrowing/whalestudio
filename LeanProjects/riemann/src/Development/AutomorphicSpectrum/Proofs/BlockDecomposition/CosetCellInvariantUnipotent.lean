import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf

namespace GlobalTheory.CompanionTheory.SwUnf

open PositivityTheory.GramSchwartzFunctions.EC

section Blocks

variable {K : Type} [Field K] {n : ℕ}

theorem lowerC_apply' (M : Matrix (Fin (n + n)) (Fin (n + n)) K) (i j : Fin n) :
    lowerC M i j = M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) := rfl

theorem lowerC_siegel_mul {y : Matrix (Fin (n + n)) (Fin (n + n)) K} (hy : IsSiegelP y)
    (W : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    lowerC (y * W) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD y * lowerC W := by
  have hy' : ∀ i j : Fin n, y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := hy
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hy', zero_mul, Finset.sum_const_zero, zero_add, GlobalTheory.CompanionTheory.RatPtsUnn.blkD]

theorem lowerC_mul_unip (X : Matrix (Fin (n + n)) (Fin (n + n)) K) (b : Matrix (Fin n) (Fin n) K) :
    lowerC (X * blk4 1 b 0 1) = lowerC X := by
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₁, Matrix.one_apply, Matrix.zero_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero]

end Blocks

variable {D : D7} {n : ℕ}

private theorem incA_injective' (D : D7) : Function.Injective (incA D) := by
  haveI : Nontrivial (AF D.host.F) :=
    inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing D.host.F ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F))
  haveI : Nontrivial (AF D.host.F ⊗[D.host.F] D.host.E) :=
    Function.Injective.nontrivial
      (Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective)
  exact (incA D).injective

theorem isUnit_det_of_mat (x : GF D n) {g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
    (h : mat (x : G D n) = g.map (incA D)) : IsUnit g.det := by
  obtain ⟨g', hg', -, hg'm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause1 (x : G D n) x.2
  have hgg : g = g' := Matrix.map_injective (incA_injective' D) (h.symm.trans hg'm)
  rw [hgg]
  exact hg'

private theorem mat_mul_eq_ite_of_hasMult {D : D7} {n : ℕ} (a b : G D n) : mat (a * b) = mat a * mat b := by
  simp only [mat, map_mul, Units.val_mul]

theorem cosetCell_rmulEquiv : ∀ {D : D7} {n : ℕ} (q : Cosets (P D n) (GF D n)) (γ : GF D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat (γ : G D n) = blk4 1 (b.map (incA D)) 0 1 → cosetCell (rmulEquiv (P D n) (GF D n) γ q) = cosetCell q := by
  intro D n q γ b h
  set q' := rmulEquiv (P D n) (GF D n) γ q with hq'
  have e3 : GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) :=
    calc GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = q' := Quotient.out_eq q'
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ q := rfl
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ (GlobalTheory.AutomorphicL2Unitary.mk _ q.out) :=
        congrArg (GlobalTheory.AutomorphicL2Unitary.rmul _ γ) (Quotient.out_eq q).symm
      _ = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) := GlobalTheory.AutomorphicL2Unitary.rmul_mk _ _
  obtain ⟨p, hp⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.mp e3
  have hp' : ((p : GF D n) : G D n) * (q'.out : G D n) = (q.out : G D n) * (γ : G D n) :=
    congrArg Subtype.val hp
  have hb : blk4 1 (b.map (incA D)) 0 1 = (blk4 1 b 0 1).map (incA D) := by
    have h1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := (incA D).mapMatrix.map_one
    have h0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := (incA D).mapMatrix.map_zero
    unfold blk4
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, h1, h0]
  have hm := congrArg mat hp'
  rw [mat_mul_eq_ite_of_hasMult, mat_mul_eq_ite_of_hasMult, h, mat_ratOf, mat_ratOf, mat_ratOf, hb, ← Matrix.map_mul,
    ← Matrix.map_mul] at hm
  have hm2 : ratOf (p : GF D n) * ratOf q'.out = ratOf q.out * blk4 1 b 0 1 :=
    Matrix.map_injective (incA_injective' D) hm
  have hpP : ((p : GF D n) : G D n) ∈ P D n := Subgroup.mem_subgroupOf.mp p.2
  have hS : IsSiegelP (ratOf (p : GF D n)) :=
    (GlobalTheory.CompanionTheory.RatPtsUnn.clause3 _ (p : GF D n).2 _ (mat_ratOf (p : GF D n))).mp hpP
  have hC : lowerC (ratOf q.out) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) * lowerC (ratOf q'.out) := by
    rw [← lowerC_mul_unip (ratOf q.out) b, ← hm2, lowerC_siegel_mul hS]
  have hU : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n))).det := by
    have hd := isUnit_det_of_mat (p : GF D n) (mat_ratOf (p : GF D n))
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero _ hS] at hd
    exact isUnit_of_mul_isUnit_right hd
  have hinj : ∀ w, GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) *ᵥ w = 0 → w = 0 := by
    intro w hw
    rw [← Matrix.one_mulVec w, ← Matrix.nonsing_inv_mul _ hU, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero]
  simp only [cosetCell, cellKer]
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [hC, ← Matrix.mulVec_mulVec]
  constructor
  · intro h0
    rw [h0, Matrix.mulVec_zero]
  · intro h0
    exact hinj _ h0

end GlobalTheory.CompanionTheory.SwUnf
