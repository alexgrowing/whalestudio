import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibInfEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Unimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.InvInvSt

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem us_exists_open (μ : Measure G) [IsHaarMeasure μ] :
    ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ U⁻¹ = U ∧ 0 < μ U ∧ μ U < ⊤ := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set U := interior V ∩ (interior V)⁻¹ with hUdef
  have h1 : (1 : G) ∈ U := ⟨mem_interior_iff_mem_nhds.2 hV1,
    by rw [Set.mem_inv, inv_one]; exact mem_interior_iff_mem_nhds.2 hV1⟩
  have hUo : IsOpen U := isOpen_interior.inter isOpen_interior.inv
  refine ⟨U, hUo, h1, ?_, hUo.measure_pos μ ⟨1, h1⟩, ?_⟩
  · rw [hUdef, Set.inter_inv, inv_inv, inter_comm]
  · exact lt_of_le_of_lt (measure_mono (inter_subset_left.trans interior_subset))
      hVc.measure_lt_top

theorem us_invInv [SigmaCompactSpace G] (μ : Measure G) [IsHaarMeasure μ]
    [IsMulRightInvariant μ] : IsInvInvariant μ := by
  have hc : μ.inv = haarScalarFactor μ.inv μ • μ := um_eq_smul_of_sigmaCompact _ _
  obtain ⟨U, hUo, -, hUi, hpos, hfin⟩ := us_exists_open μ
  have h : μ.inv U = μ U := by rw [Measure.inv_apply, hUi]
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hc1 : haarScalarFactor μ.inv μ = 1 := by
    have : ((haarScalarFactor μ.inv μ : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
      exact h
    exact_mod_cast this
  exact ⟨by rw [hc, hc1, one_smul]⟩

theorem us_rightInv_of_compat (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ]
    {S : Type*} [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S]
    [T2Space S] [MeasurableSpace S] [BorelSpace S] [SigmaCompactSpace S] (ι : S →* G)
    (μ' : Measure S) [IsHaarMeasure μ'] {Y : Type*} [MeasurableSpace Y] (νX : Measure Y)
    (s : Y → G)
    (hcompat : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * ι h') ∂μ' ∂νX) :
    IsMulRightInvariant μ' := by
  obtain ⟨U, hUo, -, -, hpos, hfin⟩ := us_exists_open μ
  set f : G → ℝ≥0∞ := U.indicator 1 with hfdef
  have hfm : Measurable f := measurable_one.indicator hUo.measurableSet
  have hI : ∫⁻ g, f g ∂μ = μ U := lintegral_indicator_one hUo.measurableSet
  refine ⟨fun k => ?_⟩
  set c := haarScalarFactor (map (· * k) μ') μ' with hcdef
  have hc : map (· * k) μ' = c • μ' := um_eq_smul_of_sigmaCompact _ _
  have h1 := hcompat (fun g => f (g * ι k)) (hfm.comp (measurable_mul_const _))
  rw [lintegral_mul_right_eq_self f (ι k)] at h1
  have hin : ∀ y, ∫⁻ h', f (s y * ι h' * ι k) ∂μ' = c * ∫⁻ h', f (s y * ι h') ∂μ' := by
    intro y
    have e1 : (fun h' => f (s y * ι h' * ι k)) = fun h' => f (s y * ι (h' * k)) := by
      funext h'
      rw [map_mul, mul_assoc]
    rw [e1]
    have e2 := lintegral_map_equiv (μ := μ') (fun h' => f (s y * ι h')) (MeasurableEquiv.mulRight k)
    have e3 : (⇑(MeasurableEquiv.mulRight k) : S → S) = (· * k) := rfl
    rw [e3, hc, lintegral_smul_measure] at e2
    rw [← e2]
    rfl
  simp_rw [hin] at h1
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← hcompat f hfm, hI] at h1
  have hc1 : c = 1 := by
    have : (c : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
      exact h1.symm
    exact_mod_cast this
  rw [hc, hc1, one_smul]

end Gen

section Spec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem us_isClosed_stab (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (X0 : Fin a → Fin M → E) :
    IsClosed ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J)) := by
  have hcont : Continuous fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) X0 := by
    show Continuous fun g : HA (AF F) σ J =>
      actTup (AF F) (HA.mat (AF F) σ J g) (ratTup (F := F) (AF F) X0)
    unfold actTup HA.mat
    refine continuous_pi fun b => Continuous.matrix_mulVec ?_ continuous_const
    exact Units.continuous_val.comp
      (continuous_subtype_val : Continuous fun g : HR (AF F) σ J => (g : GL (Fin M) (AF F ⊗[F] E)))
  have : ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J)) =
      {g | g • ratTup (F := F) (AF F) X0 = ratTup (F := F) (AF F) X0} := by
    ext g
    exact MulAction.mem_stabilizer_iff
  rw [this]
  exact isClosed_eq hcont continuous_const

def InvG : Prop := InCtx fun F E _ _ _ _ _ σ M J _a _X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → μ.IsInvInvariant

def InvS : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure → IsCompatT F E σ M J X0 μ μ' νX →
      μ'.IsInvInvariant

theorem unimodStab_holds : UnimodStab := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ _ μ hμ νX _ μ' hμ' hC
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y) →
      s y • ratTup (F := F) (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  exact us_rightInv_of_compat μ (stabT (AF F) σ J X0).subtype μ' νX s
    (fun f hf => hC.2 f hf s hs)

theorem invG_holds : InvG := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 _a ha1 ha2 X0 hT hdet μ hμ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 _a ha1 ha2 X0 hT hdet μ hμ
  exact us_invInv μ

theorem invS_holds : InvS := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ' hC
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  have : IsMulRightInvariant μ' :=
    unimodStab_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ' hC
  exact us_invInv μ'

theorem invInv_holds : InvInv := fun F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet =>
  ⟨invG_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet,
    invS_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet⟩

end Spec

end PI.VolStabSW
