import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NullMeasurableSetShearImage
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

def conjEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (N : Subgroup H)
    (γ : H) (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ⁻¹⁻¹ ∈ N) : N ≃ₜ* N where
  toFun n := ⟨γ * n * γ⁻¹, h1 n n.2⟩
  invFun n := ⟨γ⁻¹ * n * γ⁻¹⁻¹, h2 n n.2⟩
  left_inv n := by ext; simp [mul_assoc]
  right_inv n := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem map_conj_eq_self (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ N : Subgroup H) (hΓ : Countable Γ) (hNc : IsClosed (N : Set H))
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N) (hκ : κ.IsHaarMeasure)
    (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤)
    (γ : H) (hγ : γ ∈ Γ) :
    κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ := by
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨(x : N), x.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg Subtype.val hab
  set e := conjEquiv N γ (hN γ hγ) (hN γ⁻¹ (Γ.inv_mem hγ)) with he_def
  have hfun : (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = ⇑e := rfl
  rw [hfun]
  haveI : (κ.map e).IsHaarMeasure := e.isHaarMeasure_map κ
  have hsm : κ.map e = Measure.haarScalarFactor (κ.map e) κ • κ :=
    Measure.isMulLeftInvariant_eq_smul (κ.map e) κ
  set c := Measure.haarScalarFactor (κ.map e) κ

  have hqmp : Measure.QuasiMeasurePreserving e κ κ :=
    ⟨e.continuous.measurable, by rw [hsm]; exact Measure.smul_absolutelyContinuous⟩
  have hpre : IsFundamentalDomain (Γ.subgroupOf N) (e ⁻¹' 𝓝) κ := by
    refine h𝓝.preimage_of_equiv hqmp (e := fun g : Γ.subgroupOf N =>
      (⟨⟨γ⁻¹ * (g : H) * γ⁻¹⁻¹, hN γ⁻¹ (Γ.inv_mem hγ) _ (g : N).2⟩,
        by
          show γ⁻¹ * (g : H) * γ⁻¹⁻¹ ∈ Γ
          exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) g.2) (Γ.inv_mem (Γ.inv_mem hγ))⟩ : Γ.subgroupOf N)) ?_ ?_
    · constructor
      · intro a b hab
        apply Subtype.ext; apply Subtype.ext
        have := congrArg (fun x : Γ.subgroupOf N => ((x : N) : H)) hab
        simpa using this
      · intro g
        refine ⟨⟨⟨γ * (g : H) * γ⁻¹, hN γ hγ _ (g : N).2⟩, ?_⟩, ?_⟩
        · show γ * (g : H) * γ⁻¹ ∈ Γ
          exact Γ.mul_mem (Γ.mul_mem hγ g.2) (Γ.inv_mem hγ)
        · apply Subtype.ext; apply Subtype.ext; simp [mul_assoc]
    · intro g x
      apply Subtype.ext
      simp [he_def, conjEquiv, Subgroup.smul_def, mul_assoc]
  have hmeq : κ (e ⁻¹' 𝓝) = κ 𝓝 := hpre.measure_eq h𝓝
  have hmap : κ.map e 𝓝 = κ (e ⁻¹' 𝓝) := by
    have := e.toHomeomorph.toMeasurableEquiv.map_apply (μ := κ) 𝓝
    exact this
  have hne : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hc : (c : ENNReal) * κ 𝓝 = 1 * κ 𝓝 := by
    have h' : (c • κ) 𝓝 = κ 𝓝 := by rw [← hsm, hmap, hmeq]
    rw [one_mul]
    conv_rhs => rw [← h']
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hc1 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hne hfin).1 hc
  have : c = 1 := by exact_mod_cast hc1
  rw [hsm, this, one_smul]

end GlobalTheory.UnfoldNormal
