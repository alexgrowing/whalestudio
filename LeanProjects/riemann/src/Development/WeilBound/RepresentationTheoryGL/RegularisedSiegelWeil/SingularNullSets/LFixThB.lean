import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThA
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixW_C
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p n : ℕ}

section GlobalTheory

variable {R : Type}

theorem block_matrix_apply_top_right (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (Fin.castAdd n i) (Fin.natAdd n j) = b i j := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₂]

theorem submatrix_fromBlocks_mul [Ring R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one [Ring R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

end GlobalTheory

theorem adj_neg_one : adj (-1 : Mx D n n) = -1 := by
  show (Matrix.map (-1 : Mx D n n) ⇑(Formalism.L2.Theta.cA D)).transpose = -1
  rw [show Matrix.map (-1 : Mx D n n) ⇑(Formalism.L2.Theta.cA D) = (Formalism.L2.Theta.cA D).mapMatrix (-1) from rfl,
    map_neg, map_one, Matrix.transpose_neg, Matrix.transpose_one]

private theorem blk4_neg_one_lemma {R : Type} [Ring R] :
    blk4 (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = -1 := by
  rw [← block_matrix_one (R := R) (n := n)]
  delta GlobalTheory.StdUnn.blk4
  rw [show Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = -Matrix.fromBlocks 1 0 0 1 by
    rw [Matrix.fromBlocks_neg, neg_zero]]
  exact congrFun (congrFun (Matrix.submatrix_neg _) _) _

theorem mat_ww {w : G D p} (hw : IsW w) :
    mat (w * w)⁻¹ = blk4 ((-1 : GL (Fin p) (AE D)) : Matrix _ _ _) 0 0 (adj (((-1 : GL (Fin p) (AE D))⁻¹ : GL _ _) : Matrix _ _ _)) := by
  have hM : mat (w * w) = -1 := by
    rw [mat_mul, show mat w = blk4 0 1 (-1) 0 from hw, submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    exact blk4_neg_one_lemma
  have h1 := mat_mul_inv (w * w)
  rw [hM, neg_one_mul, neg_eq_iff_eq_neg] at h1
  rw [h1, inv_neg_one, Units.val_neg, Units.val_one, adj_neg_one, blk4_neg_one_lemma]

theorem good_neg {S : Finset (Pl D)} {e : AE D} {f : Mx D ρ p → ℂ} (hf : Good S e f) (c : ℂ) :
    Good S e (fun z => c * f (-z)) := by
  delta PositivityTheory.Rg.Rsw.L.Good at hf ⊢
  intro x
  beta_reduce
  have hi : IntOff S (-x) ↔ IntOff S x := by
    delta PositivityTheory.Rg.Rsw.L.IntOff
    constructor
    · intro H v hv i j
      have h1 := neg_mem (H v hv i j)
      rwa [Matrix.neg_apply, map_neg, neg_neg] at h1
    · intro H v hv i j
      rw [Matrix.neg_apply, map_neg]
      exact neg_mem (H v hv i j)
  have h := hf (-x)
  by_cases hx : IntOff S x
  · rw [if_pos hx, h, if_pos (hi.2 hx), smul_neg]
  · rw [if_neg hx, h, if_neg (fun H => hx (hi.1 H)), mul_zero]

theorem kOff_entry {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) (k l : Fin (n + n)) :
    (∀ w, compInf D.host.F D.host.E w (mat g k l) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) k l) ∧
    (∀ v ∈ S, cv D v (mat g k l) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) k l) ∧
    (∀ v ∉ S, cv D v (mat g k l) ∈ intLoc D.host.F D.host.E v) := by
  exact ⟨fun w => kOff_inf hg w k l, fun v hv => kOff_at hg hv k l, fun v hv => (kOff_int hg hv k l).1⟩

end PositivityTheory.Rg.Rsw.L.LFixTh

end
