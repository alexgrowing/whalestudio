import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenThetaTorus

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

open GlobalTheory.LeviEvalZero in

theorem GlobalTheory.ThK.evZero_stepB : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∃ ea : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F a (a + b), IsEv B G.M G₁.M 1 H'.ι (iso0 a H') ea := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁
  have P : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T.geo.hW, T.geo.hM, T.chars.heckeβ, isHecke_div T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div T.chars.resβ T.chars.resα, T.weil⟩
  exact ((GlobalTheory.T.theta_evaluation_zero_cone hKP.base).1 F E σ B a (a + (b + 2)) G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (a + b) G₁.V G₁.W H' a
    (a + b + 1) G₁.M cfg.eV cfg.hH' T₁.geo.hM).1
