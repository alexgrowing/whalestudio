import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.RightKDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IsClosedCongruenceSubgroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.NonDeg

noncomputable section

namespace PI.LocMassTypR

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
open PI.LocMassTypW

theorem kv_mul_right_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) {κ c : HA (Fv F v) σ J}
    (hκ : κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    c * κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ↔ c ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  by
  unfold Formalism.L2.SG.TypedSets.Kv at hκ ⊢
  simp only [Set.mem_setOf_eq, map_mul] at hκ ⊢
  exact Subgroup.mul_mem_cancel_right _ hκ

theorem right_invariant_compact : RightK := by
  intro F E _ _ _ _ _ σ n J ψ v Λ μG _ hSD _ _ hLat hH κ hκ A _
  haveI := hH
  haveI : LocallyCompactSpace (HA (Fv F v) σ J) := PI.LocMassTypM.lc_HA σ J v
  haveI : SecondCountableTopology (HA (Fv F v) σ J) := PI.LocMassTypM.sc_HA σ J v
  have hKc : IsCompact (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdND.isCompact_Kv σ J v Λ hSD hLat.1
  have hKo : IsOpen (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdND.isOpen_Kv σ J v Λ hSD hLat.1
  set e : HA (Fv F v) σ J ≃ᵐ HA (Fv F v) σ J := MeasurableEquiv.mulRight κ with he
  have hcoe : ∀ x, e x = x * κ := fun x => rfl
  set μ' : Measure (HA (Fv F v) σ J) := μG.map e with hμ'
  have hμ'app : ∀ s, μ' s = μG ((fun c => c * κ) ⁻¹' s) := fun s => by
    rw [hμ', MeasurableEquiv.map_apply]
    rfl
  haveI : μ'.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, hμ'app, hμ'app]
    have hpre : (fun c => c * κ) ⁻¹' ((fun x => g * x) ⁻¹' s) =
        (fun x => g * x) ⁻¹' ((fun c => c * κ) ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage, mul_assoc]
    rw [hpre, ← Measure.map_apply (measurable_const_mul g) ((measurable_mul_const κ) hs),
      MeasureTheory.map_mul_left_eq_self μG g]
  haveI : IsFiniteMeasureOnCompacts μ' := by
    refine ⟨fun C hC => ?_⟩
    rw [hμ'app]
    have hC' : IsCompact ((fun c => c * κ) ⁻¹' C) :=
      (Homeomorph.mulRight κ).isCompact_preimage.mpr hC
    exact hC'.measure_lt_top
  have hsmul := Measure.isMulLeftInvariant_eq_smul μ' μG
  have hKpre : (fun c => c * κ) ⁻¹' (Formalism.L2.SG.TypedSets.Kv σ J Λ v) = Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
    ext c
    exact kv_mul_right_iff σ J v Λ hκ
  have hm0 : μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) ≠ 0 := hKo.measure_ne_zero μG ⟨κ, hκ⟩
  have hmt : μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) ≠ ⊤ := hKc.measure_lt_top.ne
  have hc1 : ((Measure.haarScalarFactor μ' μG : NNReal) : ENNReal) = 1 := by
    have h := congrArg (fun m : Measure (HA (Fv F v) σ J) => m (Formalism.L2.SG.TypedSets.Kv σ J Λ v)) hsmul
    simp only [Measure.smul_apply, hμ'app, hKpre, ENNReal.smul_def, smul_eq_mul] at h
    have h2 : ((Measure.haarScalarFactor μ' μG : NNReal) : ENNReal) * μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) =
        1 * μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := by rw [one_mul]; exact h.symm
    first
      | exact (ENNReal.mul_left_inj hm0 hmt).mp h2
      | exact ENNReal.mul_right_cancel hm0 hmt h2
      | exact (ENNReal.mul_eq_mul_right hm0 hmt).mp h2
  rw [← hμ'app, hsmul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc1, one_mul]

end PI.LocMassTypR
