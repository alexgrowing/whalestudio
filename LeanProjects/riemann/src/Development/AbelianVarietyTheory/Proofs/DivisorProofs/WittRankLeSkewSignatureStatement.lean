import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_rank_le_skew_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (W : Spc F E n) (r' s' : ℕ), B.IsGood σ → W.IsSkew σ B r' s' →
    ∀ (c : E), c ≠ 0 → σ c = -c → ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ (c • W.J.map σ) Xf Yf →
      r ≤ r' ∧ r ≤ s' := by
  first | exact @GlobalTheory.WittBound.wittIndex_le | exact GlobalTheory.WittBound.wittIndex_le | (intros; apply GlobalTheory.WittBound.wittIndex_le <;> assumption)
