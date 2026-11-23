import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NabsDetEqOfActEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical

namespace GlobalTheory.IdealChain

theorem pi_nnreal_smul {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : NNReal) :
    (Measure.pi fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ENNReal.coe_pow]

theorem integral_scale_change_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι] (ν νs : Measure k) (d : ι → kˣ), ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ F : (ι → k) → ℂ, ∫ e, F e ∂(Measure.pi fun _ => ν) = C * ∫ e, F (fun i => (d i : k) * e i) ∂(Measure.pi fun _ => νs) := by
  intro k _ _ _ _ _ _ ι _ ν νs d hν hνs
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨a, ha0, ha⟩ : ∃ a : NNReal, 0 < a ∧ ν = a • νs :=
    ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν νs, Measure.isAddLeftInvariant_eq_smul ν νs⟩
  let g : GL ι k := ⟨Matrix.diagonal fun i => (d i : k), Matrix.diagonal fun i => ((d i)⁻¹ : kˣ),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
  have hpos := nabs_pos' (Matrix.GeneralLinearGroup.det g)
  refine ⟨(a : ℝ) ^ Fintype.card ι * nabs k (Matrix.GeneralLinearGroup.det g),
    ⟨mul_pos (pow_pos ha0 _) hpos, fun h1 h2 => isHalfPow_mul (isHalfPow_pow ?_ _) (isHalfPow_nabs _)⟩, fun F => ?_⟩
  · have h3 : (νs (𝒪[k] : Set k)).toReal ≠ 0 := by
      obtain ⟨e, he⟩ := h2
      rw [he]
      exact (Real.rpow_pos_of_pos resCard_pos _).ne'
    have h4 : (a : ℝ) = (ν (𝒪[k] : Set k)).toReal * ((νs (𝒪[k] : Set k)).toReal)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ h3, ha, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rw [h4]
    exact isHalfPow_mul h1 (isHalfPow_inv h2)
  · have h := integral_comp_mulVec_eq_smul νs g F
    have h2 : ∀ x : ι → k, g.val.mulVec x = fun i => (d i : k) * x i := by
      intro x; funext i; simp [g, Matrix.mulVec_diagonal]
    simp only [h2] at h
    have h5 : (Measure.pi fun _ : ι => ν) = (a ^ Fintype.card ι) • Measure.pi fun _ : ι => νs := by
      rw [← pi_nnreal_smul, ← ha]
    rw [h, h5, integral_smul_nnreal_measure]
    have : (nabs k (Matrix.GeneralLinearGroup.det g) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Complex.real_smul, NNReal.smul_def, Complex.real_smul]
    push_cast
    field_simp

end GlobalTheory.IdealChain
