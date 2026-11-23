import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CMColumnLocalGLStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CM_column_local_GL_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X : Matrix (Fin n) (Fin r) E), r ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (hcm : IsCMExt F E σ) (B : GL (Fin n) (Fv F v)),
    (∀ (j : Fin r) (k : Fin n), (k : ℕ) = j → ∀ a, B.1 a k = t (X a j)) → ∀ (i : Fin r) (g : GL (Fin n) (Fv F v)),
    (∀ l j : Fin n, (g.1 - 1) l j ≠ 0 → (l : ℕ) ≤ i ∧ (l : ℕ) < j) → ∀ y : Fin n → Fv F v ⊗[F] E,
    (∀ l : Fin r, l ≤ i → (((Formalism.UG.cT (σ : E →+* E) X * J).map (inclR (F := F) (Fv F v))) *ᵥ y) l = 0) →
    (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * g * B⁻¹))).1 *ᵥ y - y ∈
      Submodule.span (Fv F v ⊗[F] E) ((fun l a => inclR (F := F) (Fv F v) (X a l)) '' {l : Fin r | l ≤ i}) := by
  first | exact @GlobalTheory.LeviBlockFrame.mulVec_sub_mem_span_frame | exact GlobalTheory.LeviBlockFrame.mulVec_sub_mem_span_frame | (intros; apply GlobalTheory.LeviBlockFrame.mulVec_sub_mem_span_frame <;> assumption)
