import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem torus_diag_witt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n r m : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (Z : Matrix (Fin n) (Fin m) E), cT (σ : E →+* E) X * J * Z = 0 → cT (σ : E →+* E) Y * J * Z = 0 → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w), archMat σ J τ (projArch σ J w a) * (frm X Z Y).map τ.1 = (frm X Z Y).map τ.1 * diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ σ n r m J X Y Z hXZ hYZ t a ha w τ
  obtain ⟨hX, hY, hZ⟩ := ha.2 w τ
  have hZc : archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 := Matrix.ext fun i j => by
    have h := congrFun (hZ (fun l => Z l j)
      (funext fun i => by simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hXZ i) j)
      (funext fun i => by simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hYZ i) j)) i
    simpa [Matrix.mul_apply, mulVec, dotProduct] using h
  have e : (frm X Z Y).map τ.1 = Matrix.fromCols (X.map τ.1) (Matrix.fromCols (Z.map τ.1) (Y.map τ.1)) := by
    ext i (k | k | k) <;> rfl
  rw [e, Matrix.mul_fromCols, Matrix.mul_fromCols, hX, hY, hZc]
  ext i (k | k | k)
  · simp [Matrix.mul_diagonal, wt]
  · simp [Matrix.mul_diagonal, wt]
  · simp [Matrix.mul_diagonal, wt]

end GlobalTheory.CompanionTheory.CFin

end
