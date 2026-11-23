import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneFormHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDiffsHermitianTwistStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.ThK.LevelCuspidalComponent

theorem cuspComp_eq_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i,
      ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • (sp i).J.map σ) → ∀ φ' : GAd σ (c₀ • (sp i).J.map σ) → ℂ,
        (∀ (g : UA σ (sp i).J) (g' : GAd σ (c₀ • (sp i).J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        ∀ K : Subgroup (GAd σ (c₀ • (sp i).J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • (sp i).J.map σ) K → GlobalTheory.UAut.IsAut σ (c₀ • (sp i).J.map σ) K φ' →
        ∀ (r : ℕ) (Xf Yf : Matrix (Fin (d₁ - 2 * i)) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • (sp i).J.map σ) Xf Yf →
          ∀ S : Finset (Fin r), ¬ (∀ k ∈ S, ∀ l ≤ k, l ∈ S) → GlobalTheory.StdPar.IsCuspComp σ (c₀ • (sp i).J.map σ) Xf Yf S K φ' 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso c h0 hj i hi f hf c₀ hc₀ hJ' φ' hφ' K hK _ r Xf Yf hW S hS
  have hT := hM.triple
  have hcm : IsCMExt F E σ := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hsk := GlobalTheory.ThK.DescB.NextStep.skew_sp hσ B hT.geo.hW.skew hH hiso
  have key : ∀ j, j < G.p → ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j, ∀ c₀ : E, c₀ ≠ 0 →
      IsHermND σ (c₀ • (sp j).J.map σ) → ∀ φ' : GAd σ (c₀ • (sp j).J.map σ) → ℂ,
      (∀ (g : UA σ (sp j).J) (g' : GAd σ (c₀ • (sp j).J.map σ)), g.1 = g'.1 → φ' g' = f g) →
      ∀ K : Subgroup (GAd σ (c₀ • (sp j).J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • (sp j).J.map σ) K →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (d₁ - 2 * j)) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • (sp j).J.map σ) Xf Yf →
        ∀ S : Finset (Fin r), ¬ (∀ k ∈ S, ∀ l ≤ k, l ∈ S) → GlobalTheory.StdPar.IsCuspComp σ (c₀ • (sp j).J.map σ) Xf Yf S K φ' 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [lev_zero]
      exact GlobalTheory.T.hyperbolic_plane_form_hermitian hKP F E σ hcm (a + a') d₁ G.W (sp 0) H' hT.geo.hW.skew hH.rank hH.xx hH.yy hH.xy hH.orth hH.gram
        _ _ _ _ _ _ h0 (GlobalTheory.ThK.DescB.Nondeg.diffs_reg hKP hM c) (GlobalTheory.T.matched_diffs_hermitian_twist hKP F E σ B a a' G X om om' R Rf hM c)
    | succ j ih =>
      intro hp
      rw [lev_succ]
      have hI := hiso j (by omega)
      exact GlobalTheory.T.hyperbolic_plane_form_hermitian hKP F E σ hcm _ _ (sp j) (sp (j + 1)) (pl j) (hsk j (by omega)) hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1
        hI.2.2.2.2.1 hI.2.2.2.2.2.1 _ _ _ _ _ _ (hj j (by omega))
        (GlobalTheory.ThK.DescB.Nondeg.lev_reg hKP hM hH hiso c h0 hj j (by omega)) (ih (by omega))
  exact key i hi f hf c₀ hc₀ hJ' φ' hφ' K hK r Xf Yf hW S hS

end GlobalTheory.ThK.LevelCuspidalComponent
