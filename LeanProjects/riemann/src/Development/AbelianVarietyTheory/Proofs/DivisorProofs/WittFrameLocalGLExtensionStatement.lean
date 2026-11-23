import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLocalGLExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFrame_local_GL_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v)
    (B : GL (Fin n) (Fv F v)), (∀ (j : Fin r) (k : Fin n), (k : ℕ) = j →
      (∀ a, B.1 a k = t (X a j)) ∧ ∀ a, (B⁻¹).1 k a = t ((Formalism.UG.cT (σ : E →+* E) Y * J) j a)) →
    ∀ (i : Fin r) (k : Fin n), (k : ℕ) = i → ∀ (ϖ : Fv F v) (D : GL (Fin n) (Fv F v)), D.1 = Matrix.diagonal (Function.update 1 k ϖ) →
    ∀ e : (Fv F v ⊗[F] E)ˣ, splitProj t (e : Fv F v ⊗[F] E) = ϖ → splitProj (t.comp σ) (e : Fv F v ⊗[F] E) = 1 →
    (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * D * B⁻¹))).1 * X.map (inclR (F := F) (Fv F v)) =
        X.map (inclR (F := F) (Fv F v)) * Matrix.diagonal (Function.update 1 i (e : Fv F v ⊗[F] E)) ∧
      (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * D * B⁻¹))).1 * Y.map (inclR (F := F) (Fv F v)) =
        Y.map (inclR (F := F) (Fv F v)) * Matrix.diagonal (Function.update 1 i (sigR (Fv F v) σ ((e⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E))) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * D * B⁻¹))).1 *ᵥ (fun a => inclR (F := F) (Fv F v) (z a)) =
          fun a => inclR (F := F) (Fv F v) (z a) := by
  first | exact @GlobalTheory.SplitFrameAction.frame_action_split | exact GlobalTheory.SplitFrameAction.frame_action_split | (intros; apply GlobalTheory.SplitFrameAction.frame_action_split <;> assumption)
