import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

namespace GlobalTheory.ThK.EvAt0.GaussForm

theorem exists_schwartz_gauss_form {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : LinearMap.BilinForm ℝ E) (hs : ∀ p p', Q p p' = Q p' p) (hp : ∀ p, p ≠ 0 → 0 < Q p p) :
    ∃ G : SchwartzMap E ℂ, ∀ s, G s = Complex.exp (-(Real.pi : ℂ) * (Q s s : ℂ)) ∧
      ∀ v, fderiv ℝ (⇑G) s v = -(2 * (Real.pi : ℂ)) * (Q s v : ℂ) * G s := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ ((-Real.pi) • Q))
  have hB : ∀ x y, B x y = -Real.pi * Q x y := fun x y => rfl
  obtain ⟨G, hG⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag B (fun x hx => by
    rw [hB]
    have := mul_pos Real.pi_pos (hp x hx)
    linarith)
  refine ⟨G, fun s => ⟨?_, fun v => ?_⟩⟩
  · rw [hG, hB]; push_cast; rfl
  · have hfun : (⇑G) = fun x => Complex.ofRealCLM (Real.exp (B x x)) := funext fun x => hG x
    have h1 := (B.hasFDerivAt (x := s)).clm_apply (hasFDerivAt_id s)
    have h2 := Complex.ofRealCLM.hasFDerivAt.comp s h1.exp
    have h3 := congrArg (fun f => fderiv ℝ f s) hfun
    rw [h3.trans h2.fderiv, hG]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id, Complex.ofRealCLM_apply, hB, smul_eq_mul,
      hs v s]
    push_cast
    ring

end GlobalTheory.ThK.EvAt0.GaussForm
