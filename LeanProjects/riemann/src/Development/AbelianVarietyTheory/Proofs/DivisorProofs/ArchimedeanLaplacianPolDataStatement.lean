import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLaplacianPolData
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_laplacian_pol_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      ∃ Δ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ →ₗ[ℝ] Module.End ℂ (SInf F (Fin a × Fin (a + a'))),
        (∀ Z, ∀ f ∈ G.M.Pol B.ψ B.emb, Δ Z f ∈ G.M.Pol B.ψ B.emb) ∧
        ∀ (Z : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (γ : ℝ → GAd σ (c • G.W.J.map σ)),
          (∀ t, embArch σ (c • G.W.J.map σ) w (projArch σ (c • G.W.J.map σ) w (γ t)) = γ t) →
          (∀ t, GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) τ (projArch σ (c • G.W.J.map σ) w (γ t)) = NormedSpace.exp (t • Z)) →
          ∀ f ∈ G.M.Pol B.ψ B.emb,
            ActsD (evI F) (fun t => om (1, (toGAd hσ G.W.J hc).symm (γ t))) f (Δ Z f) := by
  first | exact @GlobalTheory.ThKFockDer.exists_fockDer | exact GlobalTheory.ThKFockDer.exists_fockDer | (intros; apply GlobalTheory.ThKFockDer.exists_fockDer <;> assumption)
