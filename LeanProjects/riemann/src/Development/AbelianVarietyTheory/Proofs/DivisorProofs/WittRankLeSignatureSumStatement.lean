import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSignatureSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_rank_le_signature_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ c : E, c ≠ 0 → σ c = -c →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf → r ≤ G.p + G.q := by
  first | exact @GlobalTheory.WittBoundSkew.wittIndex_le | exact GlobalTheory.WittBoundSkew.wittIndex_le | (intros; apply GlobalTheory.WittBoundSkew.wittIndex_le <;> assumption)
