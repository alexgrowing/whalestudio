import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualOfDualSubgroups
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallDualLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SelfDualUniq

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]

theorem fourB_nnsmul (μ : Measure V) (c : NNReal) (B : V → V → ℂ) (f : V → ℂ) (y : V) :
    fourB (c • μ) B f y = ((c : ℝ) : ℂ) * fourB μ B f y := by
  simp only [fourB, integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]

theorem fourB_const_mul (μ : Measure V) (a : ℂ) (B : V → V → ℂ) (g : V → ℂ) (y : V) :
    fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _

theorem selfDual_unique [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [BorelSpace V] {B : V → V → ℂ} {μ ν : Measure V}
    (hμ : SelfDual μ B) (hν : SelfDual ν B) (f : V → ℂ) (hf : IsTest f) (h0 : f 0 ≠ 0) : ν = μ := by
  obtain ⟨hμH, hμI⟩ := hμ
  obtain ⟨hνH, hνI⟩ := hν
  have hc := Measure.isAddLeftInvariant_eq_smul ν μ
  set c := Measure.addHaarScalarFactor ν μ
  have key := hνI f hf 0
  rw [hc] at key
  have e : fourB (c • μ) B f = fun y => ((c : ℝ) : ℂ) * fourB μ B f y := funext (fourB_nnsmul μ c B f)
  rw [e, fourB_nnsmul, fourB_const_mul, hμI f hf 0, neg_zero] at key
  have hsq : (((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) - 1) * f 0 = 0 := by linear_combination key
  have h1 : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
    have := (mul_eq_zero.1 hsq).resolve_right h0
    linear_combination this
  have h2 : (c : ℝ) * (c : ℝ) = 1 := by exact_mod_cast h1
  have h3 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
  have h4 : c = 1 := by exact_mod_cast h3
  rw [hc, h4, one_smul]

end GlobalTheory.JR.SelfDualUniq

namespace GlobalTheory.JR.SelfDualUniq

theorem isTest_fourB {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V]
    [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V) (hs : β.IsSymm) (hn : β.Nondegenerate)
    (μ : Measure V) [μ.IsAddHaarMeasure] (f : V → ℂ) (hf : IsTest f) :
    IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F V
  obtain ⟨-, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  obtain ⟨U, hU, hUinv⟩ := AbsInv.exists_nhds_invariant hf
  obtain ⟨M, N, hMU, -, -, -, hNc, hN, -⟩ := hl U hU
  have hβ : Continuous (fun p : V × V => β p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  have hev : ∀ᶠ w in 𝓝 (0 : V), ∀ x ∈ tsupport f, ψ (β x w) = 1 := by
    refine hf.2.isCompact.eventually_forall_of_forall_eventually fun x _ => ?_
    have hc : Continuous (fun z : V × V => β z.2 z.1) := hβ.comp continuous_swap
    have ho : IsOpen {z : V × V | ‖β z.2 z.1‖ < 1} := isOpen_lt (continuous_norm.comp hc) continuous_const
    have hmem : ((0 : V), x) ∈ {z : V × V | ‖β z.2 z.1‖ < 1} := by simp
    filter_upwards [ho.mem_nhds hmem] with z hz
    exact hψ.1 _ hz.le
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hev' : ∀ᶠ y' in 𝓝 y, ∀ x ∈ tsupport f, ψ (β x (y' - y)) = 1 := by
      have ht : Tendsto (fun y' : V => y' - y) (𝓝 y) (𝓝 0) := by
        have h := (continuous_sub_right y).tendsto y
        rwa [sub_self] at h
      exact ht.eventually hev
    filter_upwards [hev'] with y' hy'
    simp only [fourB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · have : β x y' = β x y + β x (y' - y) := by simp
      simp only [this, AddChar.map_add_eq_mul, hy' x hx, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · refine HasCompactSupport.intro hNc fun y hy => ?_
    have : ¬ ∀ x ∈ M, ψ (β x y) = 1 := fun h => hy ((hN y).2 h)
    push_neg at this
    obtain ⟨m, hm, hne⟩ := this
    refine AbsInv.integral_eq_zero_of_translate μ _ m _ hne fun x => ?_
    simp only [map_add, LinearMap.add_apply, AddChar.map_add_eq_mul, hUinv M hMU x m hm]
    ring

theorem selfDual_exists_unique_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → (∃! μ : Measure V, SelfDual μ (fun x y => ψ (β x y))) ∧ ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ f, IsTest f → IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  intro F E _ _ _ _ hU ψ hψ V _ _ _ _ _ _ _ β hs hn
  haveI := hU.ultraF
  haveI := hU.lcF
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F V
  obtain ⟨-, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  obtain ⟨M, N, -, hMo, hMc, -, -, -, -⟩ := hl Set.univ Filter.univ_mem
  have hM1 : IsClopen (M : Set V) := ⟨AddSubgroup.isClosed_of_isOpen M hMo, hMo⟩
  set f : V → ℂ := ⇑(LocallyConstant.charFn ℂ hM1) with hfdef
  have hf : IsTest f := ⟨(LocallyConstant.charFn ℂ hM1).isLocallyConstant,
    HasCompactSupport.intro hMc fun x hx => by simp [f, LocallyConstant.coe_charFn, hx]⟩
  have hf0 : f 0 ≠ 0 := by simp [f, LocallyConstant.coe_charFn, M.zero_mem]
  refine ⟨?_, fun μ hμ g hg => isTest_fourB ψ hψ V β hs hn μ g hg⟩
  obtain ⟨μ, hμ⟩ := EtMeas.exists_selfDual F ψ hψ V β hs hn
  exact ⟨μ, hμ, fun ν hν => selfDual_unique hμ hν f hf hf0⟩

end GlobalTheory.JR.SelfDualUniq
