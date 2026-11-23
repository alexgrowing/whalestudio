import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftPolar

theorem sesq_eq_of_diag {V : Type} [AddCommGroup V] [Module ℂ V] (B B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (h : ∀ v, B v v = B' v v) (f g : V) : B f g = B' f g := by
  have h1 := h (f + g)
  have h2 := h (f + Complex.I • g)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.conj_I, h f, h g] at h1 h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 + (1 / 2 : ℂ) * (B f g - B' f g - B g f + B' g f) * Complex.I_mul_I

theorem integral_mul_star_eq {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (Θ : Submodule ℂ (X → ℂ)) (hm : ∀ f ∈ Θ, Measurable f) (hb : ∀ f ∈ Θ, ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (M : Module.End ℂ (X → ℂ)) (hM : ∀ f ∈ Θ, M f ∈ Θ)
    (hn : ∀ f ∈ Θ, ∫⁻ x, ‖M f x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν) (f f' : X → ℂ) (hf : f ∈ Θ) (hf' : f' ∈ Θ) :
    ∫ x, M f x * star (M f' x) ∂ν = ∫ x, f x * star (f' x) ∂ν := by
  obtain ⟨B, hB, hN⟩ := GlobalTheory.ThetaMeanSquareForm.exists_form ν Θ hm hb
  have hr : ∀ v : Θ, ∃ r : ℝ, 0 ≤ r ∧ B v v = r := fun v =>
    ⟨∫ x, ‖(v : X → ℂ) x‖ ^ 2 ∂ν, integral_nonneg fun x => by positivity, by
      rw [hB]
      simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
      rw [integral_complex_ofReal]⟩
  let N : Θ →ₗ[ℂ] Θ := M.restrict hM
  let B' : Θ →ₗ[ℂ] Θ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v => B (N u) (N v))
    (fun _ _ _ => by simp only [map_add, LinearMap.add_apply])
    (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply])
    (fun _ _ _ => by simp only [map_add])
    (fun _ _ _ => by simp only [map_smul, LinearMap.map_smulₛₗ])
  have hd : ∀ v : Θ, B' v v = B v v := fun v => by
    show B (N v) (N v) = B v v
    obtain ⟨r, hr0, e⟩ := hr v
    obtain ⟨s, hs0, e'⟩ := hr (N v)
    have h1 := hn v v.2
    have h2 := hN v
    have h3 := hN (N v)
    rw [e, Complex.ofReal_re] at h2
    rw [e', Complex.ofReal_re] at h3
    have h4 : ENNReal.ofReal s = ENNReal.ofReal r := h3.symm.trans (h1.trans h2)
    rw [e, e', (ENNReal.ofReal_eq_ofReal_iff hs0 hr0).1 h4]
  have key := sesq_eq_of_diag B' B hd ⟨f, hf⟩ ⟨f', hf'⟩
  exact (hB (N ⟨f, hf⟩) (N ⟨f', hf'⟩)).symm.trans (key.trans (hB ⟨f, hf⟩ ⟨f', hf'⟩))

theorem scalar_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ M : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 M hM hn f f' hf hf'
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  let Θ : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsThetaFunO ψ S T f}
      add_mem' := GlobalTheory.WeilVacMove.isTheta_add
      zero_mem' := GlobalTheory.WeilVacMove.isTheta_zero
      smul_mem' := fun c _ h => GlobalTheory.WeilVacMove.isTheta_smul c h }
  have hb : ∀ g ∈ Θ, ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := fun g (hg : IsThetaFunO ψ S T g) => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖g (γ + w)‖ = ‖g w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hg.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  exact integral_mul_star_eq (μ.restrict 𝓕) Θ (fun g (hg : IsThetaFunO ψ S T g) => hg.cont.measurable) hb M hM hn
    f f' hf hf'

end GlobalTheory.Mem.LiftPolar

end
