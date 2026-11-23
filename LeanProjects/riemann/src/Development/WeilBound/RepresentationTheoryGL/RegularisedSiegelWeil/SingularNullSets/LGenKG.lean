import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKF
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.IntegralBlockMatrixIff

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {D : D7} {n : ℕ}

theorem map_one' {T : Type} [CommRing T] (f : AE D →+* T) : (1 : Mx D n n).map f = 1 :=
  Matrix.map_one _ (map_zero f) (map_one f)

theorem map_zero' {T : Type} [CommRing T] (f : AE D →+* T) {m p : ℕ} : (0 : Mx D m p).map f = 0 :=
  Matrix.map_zero _ (map_zero f)

theorem unit_n (Y : Mx D n n) (hY : cj (cA D) Y = Y) :
    cj (cA D) (blk4 1 Y 0 1) * Jm D n * blk4 1 Y 0 1 = Jm D n := by
  rw [conj_block_matrix, cj_one, cj_zero, hY, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

def nOf (Y : Mx D n n) (hY : cj (cA D) Y = Y) : G D n := (exists_G _ (unit_n Y hY)).choose

theorem mat_nOf (Y : Mx D n n) (hY : cj (cA D) Y = Y) : mat (nOf Y hY) = blk4 1 Y 0 1 :=
  (exists_G _ (unit_n Y hY)).choose_spec

theorem isN_nOf (Y : Mx D n n) (hY : cj (cA D) Y = Y) : IsN (nOf Y hY) := ⟨Y, mat_nOf Y hY⟩

theorem cj_Jm : cj (cA D) (Jm D n) = blk4 0 (-1) 1 0 := by
  rw [conj_block_matrix, cj_one, cj_zero, cj_neg, cj_one]

theorem unit_w : cj (cA D) (Jm D n) * Jm D n * Jm D n = Jm D n := by
  rw [cj_Jm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]; simp

def wE (D : D7) (n : ℕ) : G D n := (exists_G _ (unit_w (D := D) (n := n))).choose

theorem mat_wE : mat (wE D n) = Jm D n := (exists_G _ (unit_w (D := D) (n := n))).choose_spec

theorem isW_wE : IsW (wE D n) := mat_wE

theorem mat_wE_inv : mat (wE D n)⁻¹ = blk4 0 (-1) 1 0 :=
  mat_inv_eq (by rw [mat_wE, submatrix_fromBlocks_mul]; simp [block_matrix_one])

theorem mat_conj (Y : Mx D n n) (hY : cj (cA D) Y = Y) :
    mat (wE D n * nOf Y hY * (wE D n)⁻¹) = blk4 1 0 (-Y) 1 := by
  rw [mat_mul, mat_mul, mat_wE, mat_nOf, mat_wE_inv, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]; simp

theorem nOf_mem {S : Finset (Pl D)} (Y : Mx D n n) (hY : cj (cA D) Y = Y) (hinf : Y.map (infPart D) = 0)
    (hS : ∀ v ∈ S, Y.map (cv D v) = 0) (hint : ∀ v ∉ S, IntM v Y) : nOf Y hY ∈ KOff D n S := by
  have hinv : mat (nOf Y hY)⁻¹ = blk4 1 (-Y) 0 1 := mat_inv_eq (by rw [mat_nOf, submatrix_fromBlocks_mul]; simp [block_matrix_one])
  apply mem_KOff
  · rw [mat_nOf, block_matrix_map, hinf, map_one', map_zero', block_matrix_one]
  · intro v hv; rw [mat_nOf, block_matrix_map, hS v hv, map_one', map_zero', block_matrix_one]
  · intro v hv i j
    rw [hinv, mat_nOf]
    exact ⟨integral_block_matrix_iff.2 ⟨IntM.one, hint v hv, IntM.zero, IntM.one⟩ i j,
      integral_block_matrix_iff.2 ⟨IntM.one, (hint v hv).neg, IntM.zero, IntM.one⟩ i j⟩

theorem conj_mem {S : Finset (Pl D)} (Y : Mx D n n) (hY : cj (cA D) Y = Y) (hinf : Y.map (infPart D) = 0)
    (hS : ∀ v ∈ S, Y.map (cv D v) = 0) (hint : ∀ v ∉ S, IntM v Y) :
    wE D n * nOf Y hY * (wE D n)⁻¹ ∈ KOff D n S := by
  have hinv : mat (wE D n * nOf Y hY * (wE D n)⁻¹)⁻¹ = blk4 1 0 Y 1 :=
    mat_inv_eq (by rw [mat_conj, submatrix_fromBlocks_mul]; simp [block_matrix_one])
  have hneg : ∀ {T : Type} [CommRing T] (f : AE D →+* T), (-Y).map f = -(Y.map f) := fun f => Matrix.map_neg _ (map_neg f) _
  apply mem_KOff
  · rw [mat_conj, block_matrix_map, hneg, hinf, neg_zero, map_one', map_zero', block_matrix_one]
  · intro v hv; rw [mat_conj, block_matrix_map, hneg, hS v hv, neg_zero, map_one', map_zero', block_matrix_one]
  · intro v hv i j
    rw [hinv, mat_conj]
    exact ⟨integral_block_matrix_iff.2 ⟨IntM.one, IntM.zero, (hint v hv).neg, IntM.one⟩ i j,
      integral_block_matrix_iff.2 ⟨IntM.one, IntM.zero, hint v hv, IntM.one⟩ i j⟩

end PositivityTheory.Rg.Rsw.L.LGenK
