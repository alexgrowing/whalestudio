import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedAdaptedFlagPositiveQThird
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.ThK.DescB.CuspAut

theorem isAut_lev : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
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
        ∃ K : Subgroup (GAd σ (c₀ • (sp i).J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • (sp i).J.map σ) K ∧ GlobalTheory.UAut.IsAut σ (c₀ • (sp i).J.map σ) K φ' := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hA hI c _ _ i hi f hf c₀ hc₀ hJ φ' hφ
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hM.triple.base.cm
  have hsk := GlobalTheory.ThK.DescB.PrimeSplit.skew_sp hσ B hM.triple.geo.hW.skew hA hI i hi.le
  have hσc : σ c₀ = -c₀ := by
    by_contra hne
    have hrank : d₁ - 2 * i = d₁ - 2 * (i + 1) + 2 := (hI i hi).1
    have hzero : c₀ • (sp i).J.map σ = 0 := by
      ext k l
      have h1 := hJ.1 k l
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ] at h1
      have h2 := hsk l k
      rw [h2] at h1
      have h3 : (σ c₀ + c₀) * (sp i).J l k = 0 := by linear_combination h1
      have h4 : (sp i).J l k = 0 := (mul_eq_zero.1 h3).resolve_left fun h => hne (eq_neg_of_add_eq_zero_left h)
      simp [h2, h4]
    have : Nonempty (Fin (d₁ - 2 * i)) := ⟨⟨0, by omega⟩⟩
    exact hJ.2 (by rw [hzero]; exact Matrix.det_zero)
  obtain ⟨K, hK, -, hall⟩ := GlobalTheory.ThK.DescB.LevAutSup.lev_isAut_maxCpt hKP F E σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁
    sp pl hA hI _ (diffs_le_sup B G X om om' R Rf c) hσ c₀ hc₀ hσc i hi.le
  refine ⟨K, hK, ?_⟩
  have e : φ' = fun x => f ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ (sp i).J hc₀).symm x) := funext fun x => hφ _ x rfl
  rw [e]
  exact hall f hf

end GlobalTheory.ThK.DescB.CuspAut
