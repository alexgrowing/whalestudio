import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPlaceInducedIntertwinerExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_induced_intertwiner_exists : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v, X.Good v → ∀ t : E →ₐ[F] Fv F v,
    ∃ (P : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] IndAA (Fv F v) a a' ![chrW X.α t, chrW X.β t])
      (c : GL (Fin (a + a')) (Fv F v)),
      (∀ f, ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = f) ∧
      (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = 0 → φ ∈ augAt om v) ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁) ∧
      ∀ h ∈ UAt σ G.W (evFin F v), ∀ g : GL (Fin (a + a')) (Fv F v),
        (mat h).map (piW t) = ((c * g * c⁻¹ : GL (Fin (a + a')) (Fv F v)) : Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v)) →
        ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om (1, h)) φ φ₁ → P φ₁ = indAA (Fv F v) a a' ![chrW X.α t, chrW X.β t] g (P φ) := by
  first | exact @GlobalTheory.ZetaCoinvSplit.zeta_coinv | exact GlobalTheory.ZetaCoinvSplit.zeta_coinv | (intros; apply GlobalTheory.ZetaCoinvSplit.zeta_coinv <;> assumption)
