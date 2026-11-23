import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicColumnsLocalGLExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_columns_local_GL_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X : Matrix (Fin n) (Fin r) E), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → r ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (hcm : IsCMExt F E σ) (B : GL (Fin n) (Fv F v)),
    (∀ (j : Fin r) (k : Fin n), (k : ℕ) = j → ∀ a, B.1 a k = t (X a j)) → ∀ (i : Fin r) (g : GL (Fin n) (Fv F v)),
    (∀ l j : Fin n, (g.1 - 1) l j ≠ 0 → (l : ℕ) ≤ i ∧ (l : ℕ) < j) → ∀ j : Fin r,
    (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * g * B⁻¹))).1 *ᵥ (fun a => inclR (F := F) (Fv F v) (X a j)) -
        (fun a => inclR (F := F) (Fv F v) (X a j)) ∈
      Submodule.span (Fv F v ⊗[F] E) ((fun l a => inclR (F := F) (Fv F v) (X a l)) '' {l : Fin r | l < j ∧ l ≤ i}) := by
  first | exact @GlobalTheory.SplitUnipFrame.mulVec_sub_mem_span | exact GlobalTheory.SplitUnipFrame.mulVec_sub_mem_span | (intros; apply GlobalTheory.SplitUnipFrame.mulVec_sub_mem_span <;> assumption)
