import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqOfSetLIntegralEq
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellCompare

theorem isFundamentalDomain_of_map {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G)
    (H : Subgroup G) (Γ : Subgroup H) (𝓕 : Set G)
    (h : IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ) : IsFundamentalDomain Γ 𝓕 μ := by
  let E := Subgroup.equivMapOfInjective Γ H.subtype H.subtype_injective
  refine h.preimage_of_equiv (f := id) (e := E.symm) (Measure.QuasiMeasurePreserving.id μ)
    E.symm.bijective (fun g x => ?_)
  show (((E.symm g : Γ) : H) : G) * x = (g : G) * x
  congr 1
  have h1 : ((E (E.symm g) : Γ.map H.subtype) : G) = (g : G) := by rw [E.apply_symm_apply]
  rw [← h1, Subgroup.coe_equivMapOfInjective_apply]
  rfl

end GlobalTheory.CellCompare

theorem GlobalTheory.CellCompare.lintegral_comparison : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    (Γ Γ' : Subgroup H) [Countable Γ] [Countable Γ'] (D D' : Set H), IsFundamentalDomain Γ D ν →
    IsFundamentalDomain Γ' D' ν → ∀ (𝓕 𝓕' : Set G), IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ →
    IsFundamentalDomain (Γ'.map H.subtype) 𝓕' μ → ∀ f : G → ℝ≥0∞, Measurable f → (∀ h : H, ∀ g, f (h * g) = f g) →
    ν D' * ∫⁻ g in 𝓕, f g ∂μ = ν D * ∫⁻ g in 𝓕', f g ∂μ := by
  intro G _ _ _ _ μ _ _ H ν _ _ _ Γ Γ' _ _ D D' hD hD' 𝓕 𝓕' h𝓕 h𝓕' f hf hinv
  haveI : MeasurableSMul₂ H G := ⟨(measurable_subtype_coe.comp measurable_fst).mul measurable_snd⟩
  haveI : SMulInvariantMeasure H G μ := inferInstance
  haveI : MeasurableInv H := ⟨by
    have : Measurable fun x : H => (((x : G)⁻¹ : G)) := measurable_subtype_coe.inv
    exact Measurable.subtype_mk (f := fun x : H => ((x : G))⁻¹) (h := fun x => H.inv_mem x.2) this⟩
  haveI : MeasurableMul₂ H := ⟨by
    have : Measurable fun p : H × H => ((p.1 : G) * (p.2 : G)) :=
      (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
    exact Measurable.subtype_mk (f := fun p : H × H => ((p.1 : G) * (p.2 : G)))
      (h := fun p => H.mul_mem p.1.2 p.2.2) this⟩
  exact GlobalTheory.CovolIndep.lintegral_mul_eq ν μ Γ Γ' 𝓕 𝓕' D D'
    (GlobalTheory.CellCompare.isFundamentalDomain_of_map μ H Γ 𝓕 h𝓕)
    (GlobalTheory.CellCompare.isFundamentalDomain_of_map μ H Γ' 𝓕' h𝓕') hD hD' f hf (fun s x => hinv s x)
