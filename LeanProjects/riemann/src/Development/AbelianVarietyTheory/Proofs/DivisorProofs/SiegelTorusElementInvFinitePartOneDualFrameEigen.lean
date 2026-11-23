import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementRealComponentsOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementDualFrameRowsEigenInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameConjugateGramInvStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusInv

theorem dual_mul_compl {R : Type} [CommRing R] {m r : ℕ} (X Y : Matrix (Fin m) (Fin r) R)
    (X' Y' : Matrix (Fin r) (Fin m) R) (xx : X' * X = 0) (yy : Y' * Y = 0) (xy : X' * Y = 1) (yx : Y' * X = 1) :
    X' * (1 - X * Y' - Y * X') = 0 ∧ Y' * (1 - X * Y' - Y * X') = 0 := by
  constructor
  · rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, xx, xy]; simp
  · rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, yx, yy]; simp

theorem mapped {E : Type} [CommRing E] (f : E →+* ℂ) {m r : ℕ} (X Y : Matrix (Fin m) (Fin r) E)
    (X' Y' : Matrix (Fin r) (Fin m) E) (xx : X' * X = 0) (yy : Y' * Y = 0) (xy : X' * Y = 1) (yx : Y' * X = 1)
    (t : Fin r → ℝ) (ht : ∀ i, 0 < t i) (A B : Matrix (Fin m) (Fin m) ℂ)
    (hX : A * X.map f = X.map f * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)))
    (hY : A * Y.map f = Y.map f * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹))
    (hz : ∀ z : Fin m → E, X' *ᵥ z = 0 → Y' *ᵥ z = 0 → A *ᵥ (fun i => f (z i)) = fun i => f (z i))
    (hAB : A * B = 1) :
    Y'.map f * B = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * Y'.map f ∧
    X'.map f * B = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * X'.map f ∧
    (1 - X * Y' - Y * X').map f * B = (1 - X * Y' - Y * X').map f := by
  have hP : (1 - X * Y' - Y * X').map f = 1 - X.map f * Y'.map f - Y.map f * X'.map f := by
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_one _ (map_zero f) (map_one f)]
  obtain ⟨k1, k2⟩ := dual_mul_compl X Y X' Y' xx yy xy yx
  have hA : A * (1 - X * Y' - Y * X').map f = (1 - X * Y' - Y * X').map f := by
    ext i j
    have := hz (fun k => (1 - X * Y' - Y * X' : Matrix (Fin m) (Fin m) E) k j)
      (by funext a; exact congrFun (congrFun k1 a) j) (by funext a; exact congrFun (congrFun k2 a) j)
    exact congrFun this i
  have hne : ∀ i, ((t i : ℝ) : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (ht i).ne'
  rw [hP] at hA ⊢
  refine GlobalTheory.T.torusElement_dualFrameRows_eigen_inverse ℂ m r (X.map f) (Y.map f) (X'.map f) (Y'.map f) _ _ A B ?_ ?_ ?_ ?_ ?_ ?_ hX hY hA hAB
  · rw [← Matrix.map_mul, xx, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, yy, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, xy, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [← Matrix.map_mul, yx, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hne i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hne i)

theorem torus_inv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 ∧ ∀ τ, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) ∧ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) ∧ (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) := by
  intro D θ hθ V r X Y hW t ht a ha
  obtain ⟨hf, hr⟩ := GlobalTheory.T.siegelTorusElement_real_components_of_frame D θ hθ V r X Y t a ha
  have h1 : Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V a⁻¹ = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨?_, fun τ => ?_⟩
  · have h2 := congrArg (fun M => Matrix.map M (finPart D)) h1
    rw [Matrix.map_mul, hf, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  · obtain ⟨hX, hY, hz⟩ := hr τ
    have hAB : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *
        Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = 1 := by
      have h3 : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V a⁻¹) =
          Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) :=
        Matrix.map_mul (f := (θ τ).comp (infPart D))
      rw [← h3, h1]
      exact Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))
    exact mapped (tauE D τ) X Y _ _ hW.xx hW.yy hW.xy (GlobalTheory.T.witt_frame_conjugate_gram_inv D V r X Y hW) t ht _ _ hX hY hz hAB

end GlobalTheory.TorusInv
