import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerHaarLocalFactorCaseATwo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_haar_local_factor_case_a_two : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : Fin b × Fin (b + a') → AF F,
      (∀ (m : ℕ) (t : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) (k : K), AEStronglyMeasurable (fun l : (AE F E)ˣ => iteratedFDeriv ℝ m (fun s => (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2))) t) μ) ∧
      ∀ (m : ℕ) (t : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F), AEStronglyMeasurable (fun k : K => ∫ l, iteratedFDeriv ℝ m (fun s => (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2))) t ∂μ) μK := by
  first | exact @GlobalTheory.ConeSliceMeas.slice_deriv_aestronglyMeasurable | exact GlobalTheory.ConeSliceMeas.slice_deriv_aestronglyMeasurable | (intros; apply GlobalTheory.ConeSliceMeas.slice_deriv_aestronglyMeasurable <;> assumption)
