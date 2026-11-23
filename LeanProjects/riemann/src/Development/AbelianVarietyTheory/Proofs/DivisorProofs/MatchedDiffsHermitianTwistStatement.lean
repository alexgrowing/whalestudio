import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDiffsHermitianTwist
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_diffs_hermitian_twist : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ c : ℂ, ∀ f ∈ Diffs B G X om om' R Rf c,
      ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • G.W.J.map σ) → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
        (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        ∀ K : Subgroup (GAd σ (c₀ • G.W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • G.W.J.map σ) K →
        ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • G.W.J.map σ) Xf Yf →
          ∀ S : Finset (Fin r), ¬ (∀ k ∈ S, ∀ l ≤ k, l ∈ S) → GlobalTheory.StdPar.IsCuspComp σ (c₀ • G.W.J.map σ) Xf Yf S K φ' 0 := by
  first | exact @GlobalTheory.ThK.CuspComponentDifferences.cuspComp_diffs_eq_zero | exact GlobalTheory.ThK.CuspComponentDifferences.cuspComp_diffs_eq_zero | (intros; apply GlobalTheory.ThK.CuspComponentDifferences.cuspComp_diffs_eq_zero <;> assumption)
