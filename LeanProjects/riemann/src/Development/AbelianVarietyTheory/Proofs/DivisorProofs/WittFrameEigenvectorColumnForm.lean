import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.TorusCentRow

theorem row_scalar : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {g : GAd σ J} {k : Fin r} (γ : AF F ⊗[F] E),
    (matHom _ σ J g⁻¹).1 *ᵥ (fun i => adMat F Y i k) = γ • (fun i => adMat F Y i k) → ∀ i,
    (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1) k i =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * adMat F (cT (σ : E →+* E) Y * J) k i := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW g k γ hγ i
  set S := sigR (AF F) σ with hS
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 with hMdef
  set Mi : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g⁻¹).1 with hMidef
  have hinv : matHom (AF F) σ J g⁻¹ = (matHom (AF F) σ J g)⁻¹ := map_inv _ g
  have hMMi : M * Mi = 1 := by
    rw [hMdef, hMidef, hinv]; exact Units.mul_inv _
  have hU : cT S M * adMat F J * M = adMat F J := g.2
  have hadY : adMat F (cT (σ : E →+* E) Y * J) = cT S (adMat F Y) * adMat F J := by
    rw [adMat, Matrix.map_mul]
    congr 1
  have hJM : adMat F J * M = cT S Mi * adMat F J := by
    calc adMat F J * M = (cT S Mi * cT S M) * adMat F J * M := by
          rw [← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
      _ = cT S Mi * (cT S M * adMat F J * M) := by simp only [Matrix.mul_assoc]
      _ = cT S Mi * adMat F J := by rw [hU]
  have hcol : ∀ j, (Mi * adMat F Y) j k = γ * adMat F Y j k := by
    intro j
    have := congrFun hγ j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hrow : ∀ i, (adMat F (cT (σ : E →+* E) Y * J) * M) k i
      = S γ * adMat F (cT (σ : E →+* E) Y * J) k i := by
    intro i
    rw [hadY, Matrix.mul_assoc, hJM, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul]
    simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, hcol, map_mul,
      Finset.mul_sum, mul_assoc]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, GlobalTheory.StdPar.yx hCM hJ hW]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hkk : (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) k k = S γ := by
    rw [Matrix.mul_apply]
    simp_rw [hrow, mul_assoc, ← Finset.mul_sum, ← Matrix.mul_apply, hyx, Matrix.one_apply_eq, mul_one]
  rw [hkk, hrow]

end GlobalTheory.TorusCentRow
