import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefVFContDiffOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem apOp_sum_coef {d : ℕ} {ι : Type} (s : Finset ι) (m : ℕ) (a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (u : E d → ℂ) (x : E d) :
    apOp m (fun n w y => ∑ i ∈ s, a i n w y) u x = ∑ i ∈ s, apOp m (a i) u x := by
  simp only [apOp, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]

theorem symb_sum_coef {d : ℕ} {ι : Type} (s : Finset ι) (m : ℕ) (a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (x ξ : E d) :
    symb m (fun n w y => ∑ i ∈ s, a i n w y) x ξ = ∑ i ∈ s, symb m (a i) x ξ := by
  simp only [symb, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem exists_apOp_sumSq_pow : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ k : ℕ, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ξ : E d, symb (2 * k) a x ξ = (((∑ i, (∑ j, c (b i) j x * ξ j) ^ 2) ^ k : ℝ) : ℂ)) ∧ ∀ f : h.smoothFuns (F := ℂ), ∀ x ∈ Metric.ball (0 : E d) r, (((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f : G → ℂ) (h.expG (coordEquiv b (x))) = apOp (2 * k) a (fun y => (f : G → ℂ) (h.expG (coordEquiv b (y)))) x := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b r c ⟨hc, _, hder⟩ k
  set U : Set (E d) := Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hchart : ∀ f : G → ℂ, h.IsSmoothFun f →
      ContDiff ℝ ∞ (fun y : E d => f (h.expG (coordEquiv b y))) := by
    intro f hf
    simpa using h.contDiff_comp_coordEquiv hf 1 b
  have step : ∀ (X : 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ v : E d → ℂ,
      (∀ y ∈ U, f (h.expG (coordEquiv b y)) = v y) → ∀ x ∈ U,
      h.rightDeriv X f (h.expG (coordEquiv b x)) = ∑ j, (c X j x : ℂ) * fderiv ℝ v x (ev j) := by
    intro X f hf v hv x hx
    rw [hder f hf X x hx]
    have e : (fun y : E d => f (h.expG (coordEquiv b y))) =ᶠ[nhds x] v :=
      Filter.eventually_of_mem (hU.mem_nhds hx) hv
    rw [e.fderiv_eq]
  have hcC : ∀ i j, ContDiffOn ℝ ∞ (fun y => ((c (b i) j y : ℝ) : ℂ)) U := fun i j =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hc (b i) j)
  induction k with
  | zero =>
    refine ⟨fun _ _ _ => 1, fun _ _ => contDiffOn_const, ?_, ?_⟩
    · intro x ξ; simp [symb]
    · intro f x _
      simp [apOp_zero_one]
  | succ k ih =>
    obtain ⟨a, ha, hsa, hap⟩ := ih
    choose a1 ha1 hs1 hap1 using fun i : Fin d =>
      GlobalTheory.VFComp.vectorField_comp d (2 * k) U hU a (fun j y => ((c (b i) j y : ℝ) : ℂ)) ha (hcC i)
    choose a2 ha2 hs2 hap2 using fun i : Fin d =>
      GlobalTheory.VFComp.vectorField_comp d (2 * k + 1) U hU (a1 i) (fun j y => ((c (b i) j y : ℝ) : ℂ)) (ha1 i) (hcC i)
    have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    refine ⟨fun n w y => ∑ i, a2 i n w y, fun n w => ContDiffOn.sum fun i _ => ha2 i n w, ?_, ?_⟩
    · intro x ξ
      rw [symb_sum_coef, e2]
      simp only [hs2, hs1, hsa]
      push_cast
      rw [pow_succ', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · intro f x hx
      rw [apOp_sum_coef, e2, pow_succ', Module.End.mul_apply]
      set g := ((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f with hg
      simp only [LinearMap.sum_apply, Finset.sum_apply, Submodule.coe_sum, Module.End.mul_apply,
        IsExpLieAlgebra.coe_rightDerivEnd]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hf0 := hchart _ f.2
      have h1 : ∀ y ∈ U, h.rightDeriv (b i) (g : G → ℂ) (h.expG (coordEquiv b y)) =
          apOp (2 * k + 1) (a1 i) (fun y => (f : G → ℂ) (h.expG (coordEquiv b y))) y := by
        intro y hy
        rw [step (b i) _ g.2 _ (fun z hz => hap f z hz) y hy]
        exact hap1 i _ hf0.contDiffOn y hy
      rw [step (b i) _ (h.isSmoothFun_rightDeriv g.2 (b i)) _ h1 x hx]
      exact hap2 i _ hf0.contDiffOn x hx

end GlobalTheory.HCA
