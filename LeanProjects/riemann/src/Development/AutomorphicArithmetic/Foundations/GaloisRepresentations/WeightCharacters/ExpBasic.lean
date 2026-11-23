import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

noncomputable section

namespace UpperTheory.Gal.Wt

private theorem pow_mem_le {s m : ℤ} (h : m ≤ s) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpLe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

private theorem pow_mem_ge {s m : ℤ} (h : s ≤ m) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpGe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

private theorem circle_mul_mem_of_mem_span_of_mem_span {S T : Set (Circle → ℂ)} {P : Submodule ℂ (Circle → ℂ)}
    (h : ∀ f ∈ S, ∀ g ∈ T, (fun z => f z * g z) ∈ P) {f g : Circle → ℂ}
    (hf : f ∈ Submodule.span ℂ S) (hg : g ∈ Submodule.span ℂ T) :
    (fun z => f z * g z) ∈ P := by
  induction hf using Submodule.span_induction with
  | mem f hfS =>
    induction hg using Submodule.span_induction with
    | mem g hgT => exact h f hfS g hgT
    | zero =>
      have e : (fun z => f z * (0 : Circle → ℂ) z) = 0 := by
        funext z
        simp
      rw [e]
      exact P.zero_mem
    | add g₁ g₂ _ _ h₁ h₂ =>
      have e : (fun z => f z * (g₁ + g₂) z) = (fun z => f z * g₁ z) + (fun z => f z * g₂ z) := by
        funext z
        simp [mul_add]
      rw [e]
      exact P.add_mem h₁ h₂
    | smul c g _ h₁ =>
      have e : (fun z => f z * (c • g) z) = c • (fun z => f z * g z) := by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact P.smul_mem c h₁
  | zero =>
    have e : (fun z => (0 : Circle → ℂ) z * g z) = 0 := by
      funext z
      simp
    rw [e]
    exact P.zero_mem
  | add f₁ f₂ _ _ h₁ h₂ =>
    have e : (fun z => (f₁ + f₂) z * g z) = (fun z => f₁ z * g z) + (fun z => f₂ z * g z) := by
      funext z
      simp [add_mul]
    rw [e]
    exact P.add_mem h₁ h₂
  | smul c f _ h₁ =>
    have e : (fun z => (c • f) z * g z) = c • (fun z => f z * g z) := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact P.smul_mem c h₁

private theorem circle_comp_inv_mem_of_mem_span {S : Set (Circle → ℂ)} {P : Submodule ℂ (Circle → ℂ)}
    (h : ∀ f ∈ S, (fun z : Circle => f z⁻¹) ∈ P) {f : Circle → ℂ}
    (hf : f ∈ Submodule.span ℂ S) : (fun z : Circle => f z⁻¹) ∈ P := by
  induction hf using Submodule.span_induction with
  | mem f hfS => exact h f hfS
  | zero =>
    have e : (fun z : Circle => (0 : Circle → ℂ) z⁻¹) = 0 := by
      funext z
      simp
    rw [e]
    exact P.zero_mem
  | add f₁ f₂ _ _ h₁ h₂ =>
    have e : (fun z : Circle => (f₁ + f₂) z⁻¹) = (fun z => f₁ z⁻¹) + (fun z => f₂ z⁻¹) := by
      funext z
      simp
    rw [e]
    exact P.add_mem h₁ h₂
  | smul c f _ h₁ =>
    have e : (fun z : Circle => (c • f) z⁻¹) = c • (fun z => f z⁻¹) := by
      funext z
      simp
    rw [e]
    exact P.smul_mem c h₁

private theorem circle_zpow_mul_zpow_eq_zpow_add (m n : ℤ) :
    (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) = fun z : Circle => (z : ℂ) ^ (m + n) := by
  funext z
  rw [zpow_add₀ (Circle.coe_ne_zero z)]

private theorem circle_inv_zpow_eq_zpow_neg (m : ℤ) :
    (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) = fun z : Circle => (z : ℂ) ^ (-m) := by
  funext z
  rw [Circle.coe_inv, inv_zpow, zpow_neg]

theorem expBasic_of : ExpBasic := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_le (by omega)
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_ge (by omega)
  · intro s t hst
    constructor
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hm.trans hst, rfl⟩
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hst.trans hm, rfl⟩
  · intro c m
    exact ⟨(ExpLe m).smul_mem c (pow_mem_le le_rfl), (ExpGe m).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro c
    have e : (fun _ : Circle => c) = c • (fun z : Circle => (z : ℂ) ^ (0 : ℤ)) := by
      funext z
      simp
    rw [e]
    exact ⟨(ExpLe 0).smul_mem c (pow_mem_le le_rfl), (ExpGe 0).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro s f
    constructor
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_ge (by omega)
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_le (by omega)

end UpperTheory.Gal.Wt

end
