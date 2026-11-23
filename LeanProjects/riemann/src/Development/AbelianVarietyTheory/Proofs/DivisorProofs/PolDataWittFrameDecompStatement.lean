import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataWittFrameDecomp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSignatureSum
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pol_data_witt_frame_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S s, GlobalTheory.StdPar.IsCuspExp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) s →
            ∀ (k : Fin r) (l : ℕ), k ∈ S → l ≤ k.val → (∀ j ∈ S, j < k → j.val < l) → (l = 0 ∨ ∃ j ∈ S, j.val + 1 = l) →
            ∀ n : ℕ, n = k.val + 1 - l →
            ∀ h : l + n ≤ a + a',
            ∃ (w : HeightOneSpectrum (𝓞 E)) (τ : GlobalTheory.CuspRep.CuspSub E n)
              (ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))) (z : ℝ),
              X.Good (w.under (𝓞 F)) ∧ (GlobalTheory.CuspRep.CG.mk τ).IsUnitary ∧ τ.IsLocComp w ρ ∧
                GlobalTheory.ThK.MidJac.IsMidJacAt w a a' l h (GlobalTheory.LFun.locChar X.α w * GlobalTheory.ThK.MidJac.absPowAt w (z : ℂ))
                  (GlobalTheory.LFun.locChar X.β w * GlobalTheory.ThK.MidJac.absPowAt w (z : ℂ)) ρ.ρ := by
  first | exact @GlobalTheory.ThK.MidJacGlobal.main | exact GlobalTheory.ThK.MidJacGlobal.main | (intros; apply GlobalTheory.ThK.MidJacGlobal.main <;> assumption)
