import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWDefs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnitary

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwsHeight

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain

variable {D : D7}

theorem blk4_map_alt {R S : Type} {n : ℕ} (f : R → S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem block_matrix_conjTranspose {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) ℂ) :
    (blk4 a b c d)ᴴ = blk4 aᴴ cᴴ bᴴ dᴴ := by
  unfold blk4
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

theorem block_matrix_mul_comm_ring {R : Type} [CommRing R] {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_injective {R : Type} {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have := congrArg (fun M => Matrix.submatrix M finSumFinEquiv finSumFinEquiv) h
  simpa [blk4, Matrix.fromBlocks_inj] using this

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (x * y) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 :=
  Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))

theorem compAt_zero (θ : InfFam D) (τ : D.what₂.Tau) {k m : ℕ} : compAt θ τ (0 : Mx D k m) = 0 :=
  Matrix.map_zero _ (map_zero ((θ τ).comp (infPart D)))

theorem compAt_neg (θ : InfFam D) (τ : D.what₂.Tau) {k m : ℕ} (x : Mx D k m) : compAt θ τ (-x) = -compAt θ τ x :=
  Matrix.map_neg _ (map_neg ((θ τ).comp (infPart D))) x

theorem component_block_matrix (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) :=
  blk4_map_alt _ a b c d

theorem compAt_K_unitary (θ : InfFam D) (hθ : IsInfFam θ) (n : ℕ) (k : G D n) (hk : k ∈ K D n) (τ : D.what₂.Tau) :
    (compAt θ τ (mat k))ᴴ * compAt θ τ (mat k) = 1 := by
  have e1 : compAt θ τ (mat k) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = GlobalTheory.AdelicU.infProj (embOverOf D τ) := GlobalTheory.AdelicU.eq_infProj hθ (embOverOf D τ) rfl
  have hk' : k ∈ GlobalTheory.AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (GlobalTheory.AdelicU.mem_levelAll.1 hk').2 (placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  exact hunit

theorem local_det {n : ℕ} (α ai β β0 : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin (n + n)) (Fin (n + n)) ℂ)
    (hU : Uᴴ * U = 1) (hα : α * ai = 1) (hβ : βᴴ = β)
    (h : blk4 0 1 (-1) 0 * blk4 1 β 0 1 = blk4 α 0 0 aiᴴ * blk4 1 β0 0 1 * U) :
    ‖α.det‖ ^ 2 * (1 + β * β).det.re = 1 := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  have hM : (blk4 0 1 (-1) 0 * blk4 1 β 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 0 1 (-1) (-β) := by
    rw [block_matrix_mul_comm_ring]; simp
  have hL : (blk4 α 0 0 aiᴴ * blk4 1 β0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 α (α * β0) 0 aiᴴ := by
    rw [block_matrix_mul_comm_ring]; simp
  rw [hM, hL] at h
  have hMM : blk4 0 1 (-1) (-β) * (blk4 0 1 (-1) (-β))ᴴ =
      blk4 α (α * β0) 0 aiᴴ * (blk4 α (α * β0) 0 aiᴴ)ᴴ := by
    rw [h, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU', Matrix.one_mul]
  rw [block_matrix_conjTranspose, block_matrix_conjTranspose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring] at hMM
  have h22 := (block_matrix_injective hMM).2.2.2
  have h22' : 1 + β * β = aiᴴ * ai := by
    simpa [hβ] using h22
  have hd : (1 + β * β).det = star ai.det * ai.det := by
    rw [h22', Matrix.det_mul, Matrix.det_conjTranspose]
  have hdet : α.det * ai.det = 1 := by rw [← Matrix.det_mul, hα, Matrix.det_one]
  have hre : (1 + β * β).det.re = ‖ai.det‖ ^ 2 := by
    rw [hd, Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [hre, ← mul_pow, ← norm_mul, hdet, norm_one, one_pow]

end PositivityTheory.PfSWUS.SwsHeight

end
