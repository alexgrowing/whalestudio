import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in

theorem kapX_surjective : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • Matrix.reindex e e X.gramᵀ), Function.Surjective (GlobalTheory.SquareAgree.kapX X e hJ) := by
  intro D X d e J hJ y
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin X.rank) (AE D), u.1 = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y).submatrix e e :=
    ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom y.1, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y = M := ⟨_, rfl⟩
  obtain ⟨Gt, hGt⟩ : ∃ Gt : Matrix (Fin X.rank) (Fin X.rank) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ = Gt := ⟨_, rfl⟩
  have hy : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := y.2
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e Gt := by rw [← hGt]; rfl
  rw [hM, hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1] at hy
  have hx : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one]
  have h1 : Mᵀ * reindex e e Gt * M.map (cA D) = reindex e e Gt := by
    have := congrArg (fun A => incA D D.host.xi0⁻¹ • A) hy
    simpa only [smul_smul, hx, one_smul] using this
  have h2 : (M.submatrix e e)ᵀ * Gt * (M.submatrix e e).map (cA D) = Gt := by
    have := congrArg (fun A => A.submatrix e e) h1
    rw [← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _] at this
    simpa [reindex_apply, transpose_submatrix, submatrix_submatrix, ← Matrix.submatrix_map] using this
  have hT : Gtᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := by rw [← hGt]; exact Matrix.ext fun _ _ => rfl
  have h3 := congrArg transpose h2
  rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc, hT] at h3
  rw [← hM, ← hu] at h3
  refine ⟨(⟨u, h3⟩ : HR (AF D.host.F) D.sp.cm.sig X.gram), ?_⟩
  apply Subtype.ext
  apply Units.ext
  show reindex e e u.1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y
  rw [hu]
  ext a b
  simp

end GlobalTheory.SquareAgree
