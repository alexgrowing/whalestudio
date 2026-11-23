import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSubgroupFixesPolynomialDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_subgroup_fixes_polynomial_datum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∃ U : Subgroup (GAd σ (c • G.W.J.map σ)), IsOpen (U : Set (GAd σ (c • G.W.J.map σ))) ∧ ∀ k ∈ U, k ∈ finPts σ (c • G.W.J.map σ) → ∀ g, (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) (g * k) = (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) g := by
  first | exact @GlobalTheory.ThKLevelSmall.level | exact GlobalTheory.ThKLevelSmall.level | (intros; apply GlobalTheory.ThKLevelSmall.level <;> assumption)
