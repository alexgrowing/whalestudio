import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTowerAdaptedPlanesThird
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar GlobalTheory.ThK.LiftConst

open GlobalTheory.ThK.SplitInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_tower_adapted_planes_third : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i, IsCT (W := sp i) (pl i) f 0 → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F (sp i).J)) (Fin a' × Fin (d₁ - 2 * i)),
        (∀ x : Matrix (Fin a') (Fin (d₁ - 2 * i)) E, ∃ y z : Fin a' × Fin (d₁ - 2 * i) → F,
          co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ om₁ : UA σ G.V'.J × UA σ (sp i).J →* Module.End ℂ ((Fin a' × Fin (d₁ - 2 * i) → AF F) → ℂ),
        IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F (sp i).J) co X.α (X.α / X.β) om₁ →
      ∀ Φ ∈ schA F (Fin a' × Fin (d₁ - 2 * i)), ∀ (μ : Measure (UA σ (sp i).J)) (𝓕 : Set (UA σ (sp i).J)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ (sp i).J) 𝓕 μ →
      ∃ T : Finset (Pl F), ∀ v : Pl F, v ∉ T → SplitsFully E v → QuotTriv (UAtSub σ G.V' (evFin F v)) (liftSpace (X := G.V') (W := sp i) om₁ Φ μ 𝓕 f v) := by
  first | exact @GlobalTheory.ThK.SplitQuot.quotTriv_liftSpace | exact GlobalTheory.ThK.SplitQuot.quotTriv_liftSpace | (intros; apply GlobalTheory.ThK.SplitQuot.quotTriv_liftSpace <;> assumption)
