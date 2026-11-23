import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMeanSquareForm

open GlobalTheory.HeisOrtho

theorem exists_form {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (M : Submodule ℂ (X → ℂ))
    (hm : ∀ f ∈ M, Measurable f) (hb : ∀ f ∈ M, ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ f g : M, B f g = ∫ x, (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x) ∂ν) ∧
      ∀ f : M, ∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (B f f).re := by
  have hi : ∀ f g : M, Integrable (fun x => (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x)) ν := fun f g => by
    obtain ⟨C, hC⟩ := hb f f.2
    obtain ⟨C', hC'⟩ := hb g g.2
    refine Integrable.of_bound
      (((hm f f.2).mul (Complex.continuous_conj.measurable.comp (hm g g.2))).aestronglyMeasurable)
      (C * C') (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC x) (hC' x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f g : M => ∫ x, (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x) ∂ν) ?_ ?_ ?_ ?_, fun _ _ => rfl, fun f => ?_⟩
  · intro f f' g
    rw [← integral_add (hi f g) (hi f' g)]
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
  · intro c f g
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · intro f g g'
    rw [← integral_add (hi f g) (hi f g')]
    simp only [Submodule.coe_add, Pi.add_apply, map_add, mul_add]
  · intro c f g
    rw [smul_eq_mul, ← integral_const_mul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm]
  · rw [LinearMap.mk₂'ₛₗ_apply]
    have h1 : Integrable (fun x => ‖(f : X → ℂ) x‖ ^ 2) ν := by
      refine (hi f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Complex.norm_conj, sq]
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, Complex.ofReal_re,
      ofReal_integral_eq_lintegral_ofReal h1 (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem exists_invariant_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ f ∈ M, IsThetaFunO ψ S T f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WO S T) (f g f' g' : M), (f' : WO S T → ℂ) = heisO ψ S T u f → (g' : WO S T → ℂ) = heisO ψ S T u g → B f' g' = B f g) ∧ ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WO S T → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (B f f).re := by
  intro D ψ S T hψ M hM μ 𝓕 hμ h𝓕
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  have hb : ∀ f ∈ M, ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := fun f hf => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm ((hM f hf).quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM f hf).cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  obtain ⟨B, hB, hN⟩ := exists_form (μ.restrict 𝓕) M (fun f hf => (hM f hf).cont.measurable) hb
  refine ⟨B, fun u f g f' g' hf hg => ?_, hN⟩
  rw [hB, hB, hf, hg]
  have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
    (fun w => (f : WO S T → ℂ) w * (starRingEnd ℂ) ((g : WO S T → ℂ) w)) (by
      rintro _ ⟨γ, rfl⟩ w
      have h0 := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T (ratW T S γ) w)))
      have h1 := (hM f f.2).quasi γ w
      have h2 := (hM g g.2).quasi γ w
      show (f : WO S T → ℂ) (ratW T S γ + w) * (starRingEnd ℂ) ((g : WO S T → ℂ) (ratW T S γ + w)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]) u
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have h0 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T w u))
  show ψ (symplOH S T w u) * (f : WO S T → ℂ) (w + u) *
    (starRingEnd ℂ) (ψ (symplOH S T w u) * (g : WO S T → ℂ) (w + u)) = _
  rw [map_mul, mul_mul_mul_comm, h0, one_mul]

end GlobalTheory.ThetaMeanSquareForm

end
