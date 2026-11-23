import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefVFContDiffOn
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.WordExp

theorem isSmoothFun_foldr {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    {f : G → ℂ} (hf : h.IsSmoothFun f) : ∀ l : List 𝔤, h.IsSmoothFun (l.foldr h.rightDeriv f)
  | [] => hf
  | X :: l => h.isSmoothFun_rightDeriv (isSmoothFun_foldr h hf l) X

end GlobalTheory.WordExp

theorem GlobalTheory.WordExp.word_apOp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ l : List 𝔤, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ x ∈ Metric.ball (0 : E d) r, l.foldr h.rightDeriv f (h.expG (coordEquiv b (x))) = apOp l.length a (fun y => f (h.expG (coordEquiv b (y)))) x := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b r c hyp l
  obtain ⟨hc, -, hX⟩ := hyp
  induction l with
  | nil =>
    refine ⟨fun _ _ _ => 1, fun _ _ => contDiffOn_const, fun f _ x _ => ?_⟩
    simp only [List.foldr_nil, List.length_nil]
    rw [apOp_zero_one]
  | cons X l ih =>
    obtain ⟨a, ha, hl⟩ := ih
    have hcX : ∀ j, ContDiffOn ℝ ∞ (fun x : E d => ((c X j x : ℝ) : ℂ)) (Metric.ball 0 r) := fun j =>
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hc X j)
    obtain ⟨a', ha', -, hcomp⟩ := GlobalTheory.VFComp.vectorField_comp d l.length (Metric.ball 0 r)
      Metric.isOpen_ball a (fun j x => ((c X j x : ℝ) : ℂ)) ha hcX
    refine ⟨a', ha', fun f hf x hx => ?_⟩
    simp only [List.foldr_cons, List.length_cons]
    have hF := GlobalTheory.WordExp.isSmoothFun_foldr h hf l
    rw [hX _ hF X x hx]
    have heq : (fun y : E d => l.foldr h.rightDeriv f (h.expG (coordEquiv b y))) =ᶠ[nhds x]
        apOp l.length a (fun y => f (h.expG (coordEquiv b y))) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy using hl f hf y hy
    have hu : ContDiffOn ℝ ∞ (fun y : E d => f (h.expG (coordEquiv b y))) (Metric.ball 0 r) := by
      have := h.contDiff_comp_coordEquiv hf 1 b
      simp only [one_mul] at this
      exact this.contDiffOn
    rw [heq.fderiv_eq]
    exact hcomp _ hu x hx
