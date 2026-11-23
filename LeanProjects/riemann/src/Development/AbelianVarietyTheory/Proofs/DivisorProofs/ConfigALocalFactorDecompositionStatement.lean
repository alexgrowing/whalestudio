import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalFactorDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_local_factor_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')), IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
    (ei ≠ 0 ∧ (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ)
      (T : Finset (Pl F)), (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = G.M.vac v) →
    ∀ k ∈ K, ∀ (l : (AE F E)ˣ) (y : Fin b × Fin (b + a') → AF F) (z : ℕ),
      e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) (pure f φ))) y * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z =
        coneInfInt B G.M om ei (shiftA H H') X.ν z f (compArch σ G.V.J k) (unitArch F E l) (fun i => evI F (y i)) *
          ∏ᶠ v, coneFinInt B G.M om v (ev v) (shiftA H H') X.ν z (φ v) (compAt σ G.V.J v k) (unitAt E v l)
            (fun i => evFin F v (y i)) := by
  first | exact @GlobalTheory.ThK.ConeEulerFac.integrand_fac | exact GlobalTheory.ThK.ConeEulerFac.integrand_fac | (intros; apply GlobalTheory.ThK.ConeEulerFac.integrand_fac <;> assumption)
