import Mathlib

open MeasureTheory

namespace GlobalTheory.LatticeAut

theorem map_haar_eq_of_lattice : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N]
    [T2Space N] [MeasurableSpace N] [BorelSpace N] (Λ : Subgroup N) [Countable Λ] (ν : MeasureTheory.Measure N) [ν.IsHaarMeasure]
    (𝓕 : Set N), MeasureTheory.IsFundamentalDomain Λ 𝓕 ν → ν 𝓕 ≠ 0 → ν 𝓕 ≠ ⊤ →
    ∀ (φ : N ≃* N), Continuous φ → Continuous φ.symm → (∀ l ∈ Λ, φ l ∈ Λ) → (∀ l ∈ Λ, φ.symm l ∈ Λ) →
    MeasureTheory.Measure.map φ ν = ν := by
  intro N _ _ _ _ _ _ _ _ Λ _ ν _ 𝓕 h𝓕 h0 htop φ hφ hφ' hΛ hΛ'
  letI : MeasurableSpace Λ := ⊤
  haveI : MeasurableSMul Λ N :=
    { measurable_const_smul := fun γ => measurable_const_mul (γ : N)
      measurable_smul_const := fun _ => measurable_from_top }
  haveI : (Measure.map φ ν).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν φ hφ hφ'
  have hs := Measure.isMulLeftInvariant_eq_smul (Measure.map φ ν) ν
  have hq : Measure.QuasiMeasurePreserving φ ν ν :=
    ⟨hφ.measurable, by rw [hs]; exact Measure.AbsolutelyContinuous.rfl.smul_left _⟩
  let e : Λ → Λ := fun l => ⟨φ.symm l, hΛ' l l.2⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b hab => ?_, fun b => ⟨⟨φ b, hΛ b b.2⟩, ?_⟩⟩
    · exact Subtype.ext (φ.symm.injective (congrArg Subtype.val hab))
    · exact Subtype.ext (φ.symm_apply_apply b)
  have hA : IsFundamentalDomain Λ (φ ⁻¹' 𝓕) ν := by
    refine h𝓕.preimage_of_equiv hq he fun g x => ?_
    show φ (φ.symm g * x) = (g : N) * φ x
    rw [map_mul, MulEquiv.apply_symm_apply]
  have hm : ν (φ ⁻¹' 𝓕) = ν 𝓕 := hA.measure_eq h𝓕
  let ψ : N ≃ₜ N := { toEquiv := φ.toEquiv, continuous_toFun := hφ, continuous_invFun := hφ' }
  have hmap : Measure.map φ ν 𝓕 = ν (φ ⁻¹' 𝓕) := ψ.toMeasurableEquiv.map_apply 𝓕
  have hc1 : Measure.haarScalarFactor (Measure.map φ ν) ν = 1 := by
    have h2 : ((Measure.haarScalarFactor (Measure.map φ ν) ν : NNReal) : ENNReal) * ν 𝓕 = 1 * ν 𝓕 := by
      rw [one_mul]
      conv_rhs => rw [← hm, ← hmap, hs]
      rfl
    exact_mod_cast (ENNReal.mul_left_inj h0 htop).1 h2
  rw [hs, hc1, one_smul]

end GlobalTheory.LatticeAut
