import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_stabilizer_theta_finite : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ PolData B G.M, ∀ h, ∃ (m : ℕ) (c : Fin m → Fin b × Fin (b + a') → Af F) (φ : Fin m → (Fin b × Fin (b + a') → Af F) → ℂ),
      (∀ j, φ j ∈ SB _) ∧ ∀ k ∈ K, ∀ (l : (AE F E)ˣ) (x : Fin b × Fin (b + a') → AF F),
        e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ)) x = ∑ j, e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ)) (fun q => ((x q).1, c j q)) * φ j (fun q => (x q).2) := by
  first | exact @GlobalTheory.XTermFinParts.finite_parts | exact GlobalTheory.XTermFinParts.finite_parts | (intros; apply GlobalTheory.XTermFinParts.finite_parts <;> assumption)
