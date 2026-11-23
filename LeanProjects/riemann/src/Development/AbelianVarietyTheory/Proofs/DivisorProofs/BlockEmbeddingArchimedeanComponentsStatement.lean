import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingArchimedeanComponents
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_embedding_archimedean_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J),
    GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
    ∃ ρ : ∀ w : InfinitePlace F, GlobalTheory.CuspRep.Cinf E →+* w.Completion ⊗[F] E,
      (∀ w z, ρ w (star z) = sigR w.Completion σ (ρ w z)) ∧
      (∀ m : ∀ w : InfinitePlace F, GL (Fin d) (w.Completion ⊗[F] E), ∃ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E),
        ∀ w, Matrix.GeneralLinearGroup.map (ρ w) y = m w) ∧
      ∀ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E), ι (GlobalTheory.CuspRep.infGL E d y) ∈ infPts σ J ∧
        ∀ w, (matHom _ σ J (projArch σ J w (ι (GlobalTheory.CuspRep.infGL E d y)))).1 =
          1 + (GlobalTheory.BlockForms.blkCols h Xf).map (inclR (F := F) w.Completion) * ((Matrix.GeneralLinearGroup.map (ρ w) y).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J).map (inclR (F := F) w.Completion) +
          (GlobalTheory.BlockForms.blkCols h Yf).map (inclR (F := F) w.Completion) * (Formalism.UG.cT (sigR w.Completion σ) ((Matrix.GeneralLinearGroup.map (ρ w) y)⁻¹).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J).map (inclR (F := F) w.Completion) := by
  first | exact @GlobalTheory.BlockForms.exists_archComp_of_isBlockEmb | exact GlobalTheory.BlockForms.exists_archComp_of_isBlockEmb | (intros; apply GlobalTheory.BlockForms.exists_archComp_of_isBlockEmb <;> assumption)
