import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKE

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

private theorem blk4_mul_blk4 (A B C E A' B' C' E' : Matrix (Fin n) (Fin n) R) :
    blk4 A B C E * blk4 A' B' C' E' =
      blk4 (A * A' + B * C') (A * B' + B * E') (C * A' + E * C') (C * B' + E * E') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

private theorem cj_one' (s : R →+* R) : cj s (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold cj
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem fact_alg (s : R →+* R) (a β c u ui : Matrix (Fin n) (Fin n) R) (hu1 : u * ui = 1) (hu2 : ui * u = 1)
    (R2 : c * cj s u = u * cj s c) (C3 : cj s β * u = cj s u * β) :
    cj s (β * ui) = β * ui ∧ cj s (ui * c) = ui * c ∧
      blk4 1 (β * ui) 0 1 * blk4 (a - β * ui * c) 0 0 u * blk4 1 0 (ui * c) 1 = blk4 a β c u := by
  have hcu : cj s ui * cj s u = 1 := by
    rw [← cj_mul, hu1, cj_one']
  have hcu' : cj s u * cj s ui = 1 := by
    rw [← cj_mul, hu2, cj_one']
  have hβ : cj s β = cj s u * β * ui := by
    calc cj s β = cj s β * (u * ui) := by rw [hu1, mul_one]
      _ = cj s u * β * ui := by rw [← mul_assoc, C3]
  have hc : cj s c = ui * c * cj s u := by
    calc cj s c = (ui * u) * cj s c := by rw [hu2, one_mul]
      _ = ui * c * cj s u := by rw [mul_assoc, ← R2, ← mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [cj_mul, hβ, ← mul_assoc, ← mul_assoc, hcu, one_mul]
  · rw [cj_mul, hc, mul_assoc, hcu', mul_one]
  · have e1 : β * ui * u = β := by rw [mul_assoc, hu2, mul_one]
    have e2 : u * (ui * c) = c := by rw [← mul_assoc, hu1, one_mul]
    rw [blk4_mul_blk4, blk4_mul_blk4]
    simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one]
    rw [e1, e2, mul_assoc β ui c, sub_add_cancel]

theorem block_matrix_mul_upper_unipotent (a b c d X : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 1 X 0 1 = blk4 a (a * X + b) c (d + c * X) := by
  rw [blk4_mul_blk4]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  rw [add_comm (a * X) b, add_comm (c * X) d]

theorem upper_unipotent_block_inverse (X : Matrix (Fin n) (Fin n) R) : blk4 1 X 0 1 * blk4 1 (-X) 0 1 = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

theorem lower_unipotent_block_inverse (X : Matrix (Fin n) (Fin n) R) : blk4 1 0 X 1 * blk4 1 0 (-X) 1 = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

end PositivityTheory.Rg.Rsw.L.LGenK
