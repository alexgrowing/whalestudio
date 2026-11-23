import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKG
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.BlockMatrixMulUpperUnipotent

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

theorem cA_invol (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => change a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e) = _; rw [sig_invol]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem map_neg' {T : Type} [CommRing T] (f : AE D →+* T) (Y : Mx D n n) : (-Y).map f = -(Y.map f) := by
  exact Matrix.map_neg f (map_neg f) Y

theorem map_add' {T : Type} [CommRing T] (f : AE D →+* T) (Y Z : Mx D n n) : (Y + Z).map f = Y.map f + Z.map f := by
  exact Matrix.map_add f (map_add f) Y Z

theorem isM_of (g : G D n) (A u : Mx D n n) (h : mat g = blk4 A 0 0 u) : IsM g := by
  have hunit := mat_unit g
  rw [h] at hunit
  change cj (cA D) (blk4 A 0 0 u) * blk4 0 1 (-1) 0 * blk4 A 0 0 u = blk4 0 1 (-1) 0 at hunit
  have hcol := unit_col (cA D) A 0 0 u (unit_fromBlocks (cA D) A 0 0 u hunit)
  have hAu : cj (cA D) A * u = 1 := by
    have h21 := hcol.2.1
    rwa [mul_zero, sub_zero] at h21
  have hu1 : u * cj (cA D) A = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hAu
  have hcjmul : ∀ M N : Matrix (Fin n) (Fin n) (AE D),
      cj (cA D) (M * N) = cj (cA D) N * cj (cA D) M := by
    intro M N
    show ((M * N).map (cA D))ᵀ = (N.map (cA D))ᵀ * (M.map (cA D))ᵀ
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hcj1 : cj (cA D) (1 : Matrix (Fin n) (Fin n) (AE D)) = 1 := by
    show ((1 : Matrix (Fin n) (Fin n) (AE D)).map (cA D))ᵀ = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hA : A * cj (cA D) u = 1 := by
    have h3 := congrArg (cj (cA D)) hu1
    rwa [hcjmul, cj_cj (cA D) cA_invol, hcj1] at h3
  have hA' : cj (cA D) u * A = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hA
  refine ⟨⟨A, cj (cA D) u, hA, hA'⟩, ?_⟩
  rw [h]
  congr 1
  exact (cj_cj (cA D) cA_invol u).symm

theorem blocks_at {T : Type} [CommRing T] (f : AE D →+* T) {k : G D n} (h : (mat k).map f = 1) :
    (bA (mat k)).map f = 1 ∧ (bB (mat k)).map f = 0 ∧ (bC (mat k)).map f = 0 ∧ (bD (mat k)).map f = 1 := by
  have h2 : blk4 (bA ((mat k).map f)) (bB ((mat k).map f)) (bC ((mat k).map f)) (bD ((mat k).map f)) =
      blk4 1 0 0 1 := by
    rw [block_matrix_of_blocks, block_matrix_one, h]
  exact blockMatrixTwoByTwoFin_injective h2

end PositivityTheory.Rg.Rsw.L.LGenK
