import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThetaIntegralInv

theorem thetaIntegral_small_translate_kinf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ g ∈ KInf σ G.V' B.emb, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' (om' (g, 1) Φ) = G.M'.I om' Φ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hK ht g _ Φ hΦ
  have hp := GlobalTheory.ThK.Inhab.pairV' ht
  have hPol : GlobalTheory.ThK.PolData B G.M' ≤ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hp.good.std).mono fun v hv => hv.1.trans hv.2)
  exact integral_translate hK.base hp g Φ (hPol hΦ.1)

end GlobalTheory.ThetaIntegralInv

end
