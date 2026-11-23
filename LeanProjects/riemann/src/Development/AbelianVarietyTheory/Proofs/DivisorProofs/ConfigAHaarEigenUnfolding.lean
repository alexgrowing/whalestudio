import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDoubleIntegralExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerHaarLocalFactorCaseAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerHaarLocalFactorCaseATwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerHaarLocalFactorCaseAThree

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeSlices

theorem cone_slice_schwartz : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      ∀ x : Fin b × Fin (b + a') → AF F, ∃ g : SInf F (Fin b × Fin (b + a')),
        ∀ t, g t = cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ (x + GlobalTheory.ThetaTransform.embR t) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  choose Fm hFm using GlobalTheory.T.stabilizer_haar_local_factor_case_a hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  have hfun : ∀ k l, (⇑(Fm k l)) = fun s => (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) := fun k l => funext (hFm k l)
  obtain ⟨hm1, hm2⟩ := GlobalTheory.T.stabilizer_haar_local_factor_case_a_two hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  have hd := GlobalTheory.T.stabilizer_haar_local_factor_case_a_three hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  obtain ⟨g, hg⟩ := GlobalTheory.T.schwartz_double_integral_exists μK μ Fm (fun m t k => by simp only [hfun]; exact hm1 m t k)
    (fun m t => by simp only [hfun]; exact hm2 m t) (fun n m => by simp only [hfun]; exact hd n m)
  refine ⟨g, fun t => ?_⟩
  rw [hg]
  simp only [cone, hFm]

end GlobalTheory.ConeSlices
