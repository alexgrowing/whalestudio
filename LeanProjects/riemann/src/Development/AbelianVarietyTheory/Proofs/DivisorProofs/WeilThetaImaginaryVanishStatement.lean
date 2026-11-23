import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilThetaImaginaryVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_theta_imaginary_vanish : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∀ (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GAd σ (c • G.W.J.map σ) → ℂ)), StrictMono N → (∀ i, N i ≤ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)})) →
        (∀ i β, IsRealLine σ (c • G.W.J.map σ) β → ∀ ψ ∈ N i, lineDer β ψ ∈ N i) →
        (∀ i, ∀ k ∈ KInf σ G.W B.emb, ∀ ψ ∈ N i, (fun x => ψ (x * toGAd hσ G.W.J hc k)) ∈ N i) → m ≤ L := by
  first | exact @GlobalTheory.ThK.ThetaChain.chain_bounded | exact GlobalTheory.ThK.ThetaChain.chain_bounded | (intros; apply GlobalTheory.ThK.ThetaChain.chain_bounded <;> assumption)
