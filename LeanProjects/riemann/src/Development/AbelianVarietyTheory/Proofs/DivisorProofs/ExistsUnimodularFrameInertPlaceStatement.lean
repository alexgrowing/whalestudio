import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularFrameInertPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_frame_inertPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
  ∀ {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  ∃ (b : GL (Fin d) (w.adicCompletion E)) (δ : w.adicCompletion E),
    (∀ u, u ∈ GlobalTheory.LFun.latAt w W.L ↔ GlobalTheory.InertBigCell.InLat (w.adicCompletionIntegers E) b u) ∧
    GlobalTheory.InertBigCell.conjW σ hw δ = δ ∧
    (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))) i j ∈ w.adicCompletionIntegers E) ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det ≠ 0 ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det⁻¹ ∈ w.adicCompletionIntegers E := by
  first | exact @GlobalTheory.InertFrameUnimod.exists_frame_unimod | exact GlobalTheory.InertFrameUnimod.exists_frame_unimod | (intros; apply GlobalTheory.InertFrameUnimod.exists_frame_unimod <;> assumption)
