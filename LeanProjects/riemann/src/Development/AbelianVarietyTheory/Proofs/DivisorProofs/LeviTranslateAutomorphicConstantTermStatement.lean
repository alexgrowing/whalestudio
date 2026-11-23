import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTranslateAutomorphicConstantTerm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_translate_automorphic_constant_term : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁) (c : E) (hc : c ≠ 0)
    (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) P t 1 m →
    ∀ (φ : UA σ Y.J → ℂ) (a b : ℂ) (K : Subgroup (GAd σ (c • Y.J.map σ))),
      IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => φ ((toGAd hσ Y.J hc).symm x)) →
      IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => a * φ (m * (toGAd hσ Y.J hc).symm x) + b * φ ((toGAd hσ Y.J hc).symm x)) := by
  first | exact @GlobalTheory.ThK.LeviShift.isAutOn_levi_comb | exact GlobalTheory.ThK.LeviShift.isAutOn_levi_comb | (intros; apply GlobalTheory.ThK.LeviShift.isAutOn_levi_comb <;> assumption)
