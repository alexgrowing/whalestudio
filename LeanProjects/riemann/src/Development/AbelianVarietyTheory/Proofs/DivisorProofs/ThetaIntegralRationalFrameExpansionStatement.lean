import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRationalFrameExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_rational_frame_expansion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ (S : Finset (Fin r)) (φc : GAd σ (c • G.W.J.map σ) → ℂ),
            GlobalTheory.StdPar.IsCuspComp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) φc →
            φc ≠ 0 → ∀ k ∈ S, ∀ i : Fin r, i < k → (∀ j : Fin r, i ≤ j → j < k → j ∉ S) →
              ∃ (w : HeightOneSpectrum (𝓞 E)) (x x' : ℕ) (τ : GlobalTheory.CuspRep.CuspSub E (x + x'))
                (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ) (s₁ s₂ : ℝ),
                2 ≤ x + x' ∧ GlobalTheory.SplitWeil.IsUnram χ₁ ∧ GlobalTheory.SplitWeil.IsUnram χ₂ ∧
                (∀ u, ‖(χ₁ u : ℂ)‖ = 1) ∧ (∀ u, ‖(χ₂ u : ℂ)‖ = 1) ∧ (x = 1 → x' = 1 → 1 < |s₁ - s₂|) ∧
                ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
                  (Q : Representation ℂ (GL (Fin (x + x')) (w.adicCompletion E)) V),
                  GlobalTheory.SmGL.IsSubquotient Q (GlobalTheory.SmGL.prod₂
                    (GlobalTheory.SmGL.detRep (Fin x) (χ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (s₁ : ℂ)))
                    (GlobalTheory.SmGL.detRep (Fin x') (χ₂ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (s₂ : ℂ)))) ∧
                  ∃ f : Q.IntertwiningMap (τ.locRep w), f ≠ 0 := by
  first | exact @GlobalTheory.CuspBlock.block_bridge | exact GlobalTheory.CuspBlock.block_bridge | (intros; apply GlobalTheory.CuspBlock.block_bridge <;> assumption)
