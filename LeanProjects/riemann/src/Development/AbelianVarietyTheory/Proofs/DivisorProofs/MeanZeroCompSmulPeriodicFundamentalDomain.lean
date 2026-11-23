import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeanFundamentalDomainEqOfPeriodic
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem mean_zero_comp_smul_of_periodic :
    ∀ (n : Type) [Fintype n] (L : AddSubgroup (n → ℝ)) [Countable L] (D : Set (n → ℝ)) (k : (n → ℝ) → ℂ) (q : ℝ), 0 < q → MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → 0 < MeasureTheory.volume D → MeasureTheory.volume D < ⊤ → Continuous k → (∃ C : ℝ, ∀ s, ‖k s‖ ≤ C) → (∀ p ∈ L, ∀ s, k (s + p) = k s) → ∫ s in D, k s = 0 → ∀ (L₁ : AddSubgroup (n → ℝ)) [Countable L₁] (D₁ : Set (n → ℝ)), MeasureTheory.IsAddFundamentalDomain L₁ D₁ MeasureTheory.volume → MeasureTheory.volume D₁ < ⊤ → (∀ p ∈ L₁, ∀ s, k (q • (s + p)) = k (q • s)) → ∫ s in D₁, k (q • s) = 0 := by
  intro n _ L _ D k q hq hD hDpos hDfin hk hb hper h0 L₁ _ D₁ hD₁ hD₁fin hper₁
  have hq0 : q ≠ 0 := hq.ne'
  have hqi : q⁻¹ ≠ 0 := inv_ne_zero hq0
  let φ : (n → ℝ) →+ (n → ℝ) := DistribMulAction.toAddMonoidHom (n → ℝ) q⁻¹
  have hφ : Function.Injective φ := fun x y h => by
    simpa [φ, smul_right_inj hqi] using h
  let L' : AddSubgroup (n → ℝ) := L.map φ
  let eL : L ≃+ L' := AddSubgroup.equivMapOfInjective L φ hφ
  haveI : Countable L' := Countable.of_equiv L eL.toEquiv
  let f : (n → ℝ) ≃ (n → ℝ) := (Homeomorph.smulOfNeZero q⁻¹ hqi).toEquiv
  have hf : ∀ x, f x = q⁻¹ • x := fun x => rfl
  have hfs : ∀ x, f.symm x = q • x := fun x => by
    apply f.injective
    rw [Equiv.apply_symm_apply, hf, smul_smul, inv_mul_cancel₀ hq0, one_smul]
  have hD' : IsAddFundamentalDomain L' (f '' D) volume := by
    refine hD.image_of_equiv f ?_ eL.symm.toEquiv ?_
    · have : (f.symm : (n → ℝ) → (n → ℝ)) = fun x => q • x := funext hfs
      rw [this]
      exact Measure.quasiMeasurePreserving_smul volume hq0
    · intro g x
      show f ((eL.symm g : L) +ᵥ x) = g +ᵥ f x
      have hg : ((g : L') : n → ℝ) = q⁻¹ • ((eL.symm g : L) : n → ℝ) := by
        conv_lhs => rw [← eL.apply_symm_apply g]
        rfl
      rw [AddSubgroup.vadd_def, AddSubgroup.vadd_def, vadd_eq_add, vadd_eq_add, hf, hf, smul_add, hg]
  have himg : f '' D = q⁻¹ • D := by
    ext x; simp [hf, Set.mem_smul_set]
  rw [himg] at hD'
  have hvol : volume (q⁻¹ • D) = ENNReal.ofReal |q⁻¹ ^ Module.finrank ℝ (n → ℝ)| * volume D :=
    Measure.addHaar_smul volume q⁻¹ D
  have hvne0 : volume (q⁻¹ • D) ≠ 0 := by
    rw [hvol]
    refine mul_ne_zero ?_ hDpos.ne'
    simpa using abs_pos.2 (pow_ne_zero (Module.finrank ℝ (n → ℝ)) hqi)
  have hvfin : volume (q⁻¹ • D) < ⊤ := by
    rw [hvol]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDfin
  have hint0 : ∫ s in q⁻¹ • D, k (q • s) = 0 := by
    rw [Measure.setIntegral_comp_smul_of_pos volume k (q⁻¹ • D) hq, smul_smul,
      mul_inv_cancel₀ hq0, one_smul, h0, smul_zero]
  have hperL' : ∀ p ∈ L', ∀ s, k (q • (s + p)) = k (q • s) := by
    intro p hp s
    obtain ⟨p0, hp0, rfl⟩ := AddSubgroup.mem_map.1 hp
    have : q • (s + φ p0) = q • s + p0 := by
      simp [φ, smul_add, smul_smul, mul_inv_cancel₀ hq0]
    rw [this, hper p0 hp0]
  obtain ⟨C, hC⟩ := hb
  have key := mean_fundamentalDomain_eq_of_periodic n L' L₁ (q⁻¹ • D) D₁ (fun s => k (q • s))
    hD' hD₁ hvfin hD₁fin (hk.comp (continuous_const_smul q)) ⟨C, fun s => hC _⟩ hperL' hper₁
  rw [hint0, mul_zero] at key
  have hre : ((volume (q⁻¹ • D)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hvne0 hvfin.ne).ne'
  exact (mul_eq_zero.1 key).resolve_left hre

end GlobalTheory
