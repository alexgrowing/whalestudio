import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalRealPlaceScaling
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.LocTypeGood
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_local_real_place_scaling : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ (c : ℂ) (v : Pl F), X.Good v → ∀ (τ : E →ₐ[F] Fv F v) (hcm : IsCMExt F E σ) (ε : F)
    (herm : ∀ i j, σ (G.W.J j i) = algebraMap F E ε * G.W.J i j) (hJ : IsUnit (G.W.J.map τ).det) (x : ℕ), x = a →
    ∀ e : Fin (x + a') ≃ Fin (a + a'), ∀ f ∈ Diffs B G X om om' R Rf c,
      HasLocType hcm τ G.W.J ε herm hJ e (chrW X.α τ) (chrW X.β τ) f := by
  first | exact @GlobalTheory.LocTypeDiffs.diffs_locType | exact GlobalTheory.LocTypeDiffs.diffs_locType | (intros; apply GlobalTheory.LocTypeDiffs.diffs_locType <;> assumption)
