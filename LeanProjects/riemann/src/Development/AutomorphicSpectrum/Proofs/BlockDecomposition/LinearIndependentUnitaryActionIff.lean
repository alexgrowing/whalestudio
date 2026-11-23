import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree

theorem linearIndependent_gl_mulVec {K : Type} [CommRing K] {M n : ℕ} (g : GL (Fin M) K)
    (X : Fin n → Fin M → K) (hX : LinearIndependent K X) :
    LinearIndependent K (fun a => (g : Matrix (Fin M) (Fin M) K).mulVec (X a)) := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) := by
    intro x y hxy
    have h2 := congrArg (((g⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K).mulVec) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2
  exact hX.map' (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) (LinearMap.ker_eq_bot.2 hinj)

theorem actW_linearIndependent_iff : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) (actW R σ J h X) ↔ LinearIndependent (R ⊗[F] E) X := by
  intro F E _ _ _ R _ _ σ M n J h X
  set g := HA.mat R σ J h with hg
  have hact : actW R σ J h X = fun a => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (X a) := rfl
  refine ⟨fun hY => ?_, fun hX => ?_⟩
  · have h2 := linearIndependent_gl_mulVec g⁻¹ _ hY
    have h3 : (fun a => ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec
        (actW R σ J h X a)) = X := by
      funext a
      rw [hact]
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rwa [h3] at h2
  · rw [hact]
    exact linearIndependent_gl_mulVec g X hX

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree
