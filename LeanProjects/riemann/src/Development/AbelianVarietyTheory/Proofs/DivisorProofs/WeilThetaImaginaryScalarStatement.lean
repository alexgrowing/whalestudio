import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilThetaImaginaryScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_theta_imaginary_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∀ (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      (∀ ψ ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)}), IsSm σ (c • G.W.J.map σ) ψ) ∧ (∀ β, IsRealLine σ (c • G.W.J.map σ) β → ∀ ψ ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)}), lineDer β ψ ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)})) ∧
      (∀ k ∈ KInf σ G.W B.emb, ∀ ψ ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)}), (fun x => ψ (x * toGAd hσ G.W.J hc k)) ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)})) ∧
      Module.rank ℂ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)}) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.ThK.ZFinSmallStab.span_theta_stable | exact GlobalTheory.ThK.ZFinSmallStab.span_theta_stable | (intros; apply GlobalTheory.ThK.ZFinSmallStab.span_theta_stable <;> assumption)
