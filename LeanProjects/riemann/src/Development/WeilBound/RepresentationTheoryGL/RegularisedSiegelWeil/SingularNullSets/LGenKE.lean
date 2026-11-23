import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKD

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

section GlobalTheory

variable {R : Type} [CommRing R] {n : ℕ}

theorem submatrix_fromBlocks_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _, fromBlocks_multiply]

theorem block_matrix_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4; rw [fromBlocks_one, Matrix.submatrix_one_equiv]

theorem conj_block_matrix (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R) :
    cj s (blk4 a b c d) = blk4 (cj s a) (cj s c) (cj s b) (cj s d) := by
  unfold blk4; rw [← cj_fromBlocks]; rfl

theorem block_matrix_map {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4; rw [← fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_injective {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R} (h : blk4 a b c d = blk4 a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have : fromBlocks a b c d = fromBlocks a' b' c' d' := by
    have := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
    simpa [blk4, Matrix.submatrix_submatrix] using this
  exact Matrix.fromBlocks_inj.1 this

def bA (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
def bB (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
def bC (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
def bD (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem block_matrix_of_blocks (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : blk4 (bA M) (bB M) (bC M) (bD M) = M := by
  unfold blk4 bA bB bC bD
  rw [fromBlocks_toBlocks, Matrix.submatrix_submatrix]
  simp

theorem unit_fromBlocks (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R)
    (h : cj s (blk4 a b c d) * blk4 0 1 (-1) 0 * blk4 a b c d = blk4 0 1 (-1) 0) :
    cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0 := by
  rw [conj_block_matrix, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨h1, h2, h3, h4⟩ := blockMatrixTwoByTwoFin_injective h
  rw [cj_fromBlocks, fromBlocks_multiply, fromBlocks_multiply, h1, h2, h3, h4]

theorem unit_col (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R)
    (h : cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0) :
    cj s a * c = cj s c * a ∧ cj s a * d - cj s c * b = 1 ∧ cj s b * d = cj s d * b := by
  rw [cj_fromBlocks, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    zero_add, add_zero] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← h1]; noncomm_ring
  · rw [← h2]; noncomm_ring
  · rw [← sub_eq_zero, ← h4]; noncomm_ring

end GlobalTheory

section G

variable {D : D7} {n : ℕ}

abbrev Jm (D : D7) (n : ℕ) : Mx D (n + n) (n + n) := blk4 0 1 (-1) 0

theorem Jst_map : (Jst D n).map (inclR (AF D.host.F)) = Jm D n := by
  rw [Jst, block_matrix_map]
  have e : ((-1 : Matrix (Fin n) (Fin n) D.host.E)).map (inclR (F := D.host.F) (AF D.host.F)) = -1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp [e]

theorem mat_unit (g : G D n) : cj (cA D) (mat g) * Jm D n * mat g = Jm D n := by
  rw [← Jst_map]; exact g.2

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp [mat]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp [mat]

theorem mat_inv_mul (g : G D n) : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem mat_inv_eq {g : G D n} {N : Mx D (n + n) (n + n)} (h : mat g * N = 1) : mat g⁻¹ = N := by
  calc mat g⁻¹ = mat g⁻¹ * (mat g * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

theorem Jm_inv : blk4 (0 : Mx D n n) (-1) 1 0 * Jm D n = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

theorem exists_G (M : Mx D (n + n) (n + n)) (hM : cj (cA D) M * Jm D n * M = Jm D n) : ∃ g : G D n, mat g = M := by
  have h1 : (blk4 (0 : Mx D n n) (-1) 1 0 * cj (cA D) M * Jm D n) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cj (cA D) M), hM, Jm_inv]
  have h2 := mul_eq_one_comm.1 h1
  let u : GL (Fin (n + n)) (AE D) := ⟨M, _, h2, h1⟩
  have hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
    change cj (cA D) M * (Jst D n).map (inclR (AF D.host.F)) * M = (Jst D n).map (inclR (AF D.host.F))
    rw [Jst_map]; exact hM
  exact ⟨⟨u, hu⟩, rfl⟩

end G

end PositivityTheory.Rg.Rsw.L.LGenK
