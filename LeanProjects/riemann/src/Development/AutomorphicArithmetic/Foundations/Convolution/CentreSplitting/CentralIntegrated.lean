import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute

open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.Dp

attribute [local instance 100] LieRing.ofAssociativeRing

section General

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (π : BanachRep G E)

theorem kernel_uAction (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) (f : h.smoothFuns (F := ℂ))
    (hf : h.IsTestFunction fun g => f.1 g⁻¹) :
    h.IsTestFunction (fun g => (h.rightUAction u f).1 g⁻¹) ∧ ∀ w : E,
      (h.uAction π u ⟨π.integrated μ (fun g => f.1 g⁻¹) w, h.isSmoothVector_integrated π μ hf w⟩ : E) =
        π.integrated μ (fun g => (h.rightUAction u f).1 g⁻¹) w := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing f with
  | algebraMap r =>
    have e : (fun g => (h.rightUAction (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (algebraMap ℝ _ r)) f).1 g⁻¹) =
        fun g => (r : ℂ) * f.1 g⁻¹ := by
      rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply]
      rfl
    rw [e]
    refine ⟨hf.const_mul _, fun w => ?_⟩
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, IsExpLieAlgebra.integrated_const_mul_kernel]
    exact (Complex.coe_smul r _).symm
  | ι x =>
    have e : (fun g => (h.rightUAction (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (TensorAlgebra.ι ℝ x)) f).1 g⁻¹) =
        h.convDeriv (h.ofLie x) fun g => f.1 g⁻¹ := by
      show (fun g => (h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ x) f).1 g⁻¹) = _
      rw [IsExpLieAlgebra.rightUAction_ι, IsExpLieAlgebra.coe_rightDerivEnd]
      funext g
      simp only [IsExpLieAlgebra.convDeriv, inv_inv]
    rw [e]
    refine ⟨hf.convDeriv _, fun w => ?_⟩
    show (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ x) ⟨_, h.isSmoothVector_integrated π μ hf w⟩ : E) = _
    rw [IsExpLieAlgebra.uAction_ι, IsExpLieAlgebra.coe_derivEnd, h.derivOp_integrated_convDeriv μ π hf]
  | mul a b ha hb =>
    obtain ⟨h1, h2⟩ := hb f hf
    obtain ⟨h3, h4⟩ := ha _ h1
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply]
    refine ⟨h3, fun w => ?_⟩
    rw [Module.End.mul_apply, ← h4 w]
    congr 2
    exact Subtype.ext (h2 w)
  | add a b ha hb =>
    obtain ⟨h1, h2⟩ := hb f hf
    obtain ⟨h3, h4⟩ := ha f hf
    rw [map_add, map_add, map_add, LinearMap.add_apply]
    refine ⟨h3.add h1, fun w => ?_⟩
    rw [LinearMap.add_apply, Submodule.coe_add, h2, h4]
    exact (h.integrated_add_kernel μ π h3 h1 w).symm

theorem central_map (hπ : ∀ g, ‖π g‖ ≤ 1) {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra} (hz : z ∈ h.centerU) {g : G}
    (hg : g ∈ Subgroup.closure (Set.range h.expG)) : ∀ {v : E} (hv : h.IsSmoothVector π v),
      (h.uAction π z ⟨π g v, h.isSmoothVector_map π hv _⟩ : E) = π g (h.uAction π z ⟨v, hv⟩) := by
  induction hg using Subgroup.closure_induction'' with
  | one => intro v hv; simp only [BanachRep.map_one_apply]
  | mem x hx => obtain ⟨X, rfl⟩ := hx; exact fun hv => h.uAction_map_expG π hπ hz hv X
  | inv_mem x hx => obtain ⟨X, rfl⟩ := hx; rw [← h.expG_neg]; exact fun hv => h.uAction_map_expG π hπ hz hv _
  | mul x y _ _ hx hy =>
    intro v hv
    simp only [BanachRep.map_mul_apply]
    rw [hx (h.isSmoothVector_map π hv y), hy hv]

theorem central_integrated (hπ : ∀ g, ‖π g‖ ≤ 1) (hG : Subgroup.closure (Set.range h.expG) = ⊤)
    {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra} (hz : z ∈ h.centerU) {f : G → ℂ} (hf : h.IsTestFunction f) {w : E}
    (hw : h.IsSmoothVector π w) :
    (h.uAction π z ⟨π.integrated μ f w, h.isSmoothVector_integrated π μ hf w⟩ : E) = π.integrated μ f (h.uAction π z ⟨w, hw⟩) := by
  obtain ⟨L, hL⟩ := h.exists_wordSum π z
  refine (hL ⟨_, h.isSmoothVector_integrated π μ hf w⟩).trans ((h.wordSum_integrated π μ hπ hw hf L).trans ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  exact congrArg (f g • ·) ((hL ⟨π g w, h.isSmoothVector_map π hw _⟩).symm.trans
    (central_map h π hπ hz (hG ▸ Subgroup.mem_top g) hw))

end General

end UpperTheory.ConvolutionTheory.Dp
