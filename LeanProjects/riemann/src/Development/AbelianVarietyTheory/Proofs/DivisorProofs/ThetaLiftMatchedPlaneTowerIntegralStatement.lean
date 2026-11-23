import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMatchedPlaneTowerIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_matched_plane_tower_integral : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i, IsCT (W := sp i) (pl i) f 0 →
      ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • (sp i).J.map σ) → ∀ φ' : GAd σ (c₀ • (sp i).J.map σ) → ℂ,
        (∀ (g : UA σ (sp i).J) (g' : GAd σ (c₀ • (sp i).J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        (Matrix.of fun k (_ : Fin 1) => (pl i).x k) ≠ 0 ∧
        Formalism.UG.cT (σ : E →+* E) (Matrix.of fun k (_ : Fin 1) => (pl i).x k) * (c₀ • (sp i).J.map σ) * (Matrix.of fun k (_ : Fin 1) => (pl i).x k) = 0 ∧
        GlobalTheory.UAut.IsConstTerm σ (c₀ • (sp i).J.map σ) (Matrix.of fun k (_ : Fin 1) => (pl i).x k) φ' 0 := by
  first | exact @GlobalTheory.IsoLineCT.isConstTerm_isoPlane | exact GlobalTheory.IsoLineCT.isConstTerm_isoPlane | (intros; apply GlobalTheory.IsoLineCT.isConstTerm_isoPlane <;> assumption)
