import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixDiagonalColumnAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_diagonal_column_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E)
    (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) (e : (Fv F v ⊗[F] E)ˣ) (i : Fin r),
    (matHom _ σ J x).1 * X.map (inclR (F := F) (Fv F v)) =
        X.map (inclR (F := F) (Fv F v)) * Matrix.diagonal (Function.update 1 i (e : Fv F v ⊗[F] E)) →
    (matHom _ σ J x).1 * Y.map (inclR (F := F) (Fv F v)) =
        Y.map (inclR (F := F) (Fv F v)) * Matrix.diagonal (Function.update 1 i (sigR (Fv F v) σ ((e⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E))) →
    (∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        (matHom _ σ J x).1 *ᵥ (fun a => inclR (F := F) (Fv F v) (z a)) = fun a => inclR (F := F) (Fv F v) (z a)) →
    GlobalTheory.LeviBlockRealization.IsBlockCentre σ J X Y i (GlobalTheory.Doubling.ideleAt F E v e) (emb σ J v x) := by
  first | exact @GlobalTheory.LeviBlockRealization.LocEmb.isPositionCentre_emb | exact GlobalTheory.LeviBlockRealization.LocEmb.isPositionCentre_emb | (intros; apply GlobalTheory.LeviBlockRealization.LocEmb.isPositionCentre_emb <;> assumption)
