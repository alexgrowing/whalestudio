import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalInducedSpaceIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_local_induced_space_iso : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin (a + a')) (Fv F v)),
      ∃ e : Rf.Pi v ≃ₗ[ℂ] GlobalTheory.KSplit.indSp a a' (chrW X.α t) (chrW X.β t),
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ g : GL (Fin (a + a')) (Fv F v),
            (e (Rf.p v φ₁) : GL (Fin (a + a')) (Fv F v) → ℂ) g =
              (e (Rf.p v φ) : GL (Fin (a + a')) (Fv F v) → ℂ) (g * GlobalTheory.KSplit.locMat t c h) := by
  first | exact @GlobalTheory.KSplitIdent.exists_equiv_indSp | exact GlobalTheory.KSplitIdent.exists_equiv_indSp | (intros; apply GlobalTheory.KSplitIdent.exists_equiv_indSp <;> assumption)
