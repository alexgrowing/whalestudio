import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ContinuousAinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe

noncomputable section

open scoped ContDiff
open MeasureTheory Set Filter Topology Complex

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

theorem kills_linear_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ) (L : V →L[ℝ] ℝ)
    (hT : ∀ (t : ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * ((t • L) x : ℂ)) * f x) →
      T f' = T f)
    (f g : SchwartzMap V ℂ) (hg : ∀ x, g x = (L x : ℂ) * f x) : T g = 0 := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ)) (continuous_norm.comp T.continuous)
  let B : ℕ × ℕ → ℝ := fun m => 3 * 2 ^ m.2 * (1 + ‖L‖) ^ (m.2 + 2) *
    (2 ^ (m.1 + 2) * ((Finset.Iic (m.1 + 2, m.2)).sup
      fun (q : ℕ × ℕ) => SchwartzMap.seminorm ℂ q.1 q.2) f)
  have hB0 : ∀ m, 0 ≤ B m := by
    intro m
    have := apply_nonneg ((Finset.Iic (m.1 + 2, m.2)).sup
      fun (q : ℕ × ℕ) => SchwartzMap.seminorm ℂ q.1 q.2) f
    positivity
  have hS : 0 ≤ ∑ m ∈ s, B m := Finset.sum_nonneg fun m _ => hB0 m
  have hK : 0 ≤ (C : ℝ) * ∑ m ∈ s, B m := mul_nonneg C.2 hS
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖T g‖ ≤ t * ((C : ℝ) * ∑ m ∈ s, B m) := by
    intro t ht0 ht1
    have hG := GlobalTheory.CharFormDeriv.hasTemperateGrowth_char L t
    let M : SchwartzMap V ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : V => cexp (I * ↑t * ↑(L x))) f
    have hM : ∀ x, M x = cexp (I * ↑t * ↑(L x)) * f x := by
      intro x
      simp [M, SchwartzMap.smulLeftCLM_apply_apply hG]
    have hTM : T M = T f := by
      apply hT t f M
      intro x
      rw [hM x]
      simp [mul_assoc]
    let u : SchwartzMap V ℂ := (t : ℂ)⁻¹ • M - I • g - (t : ℂ)⁻¹ • f
    have hu : ∀ x, u x = GlobalTheory.CharFormDeriv.rem t (L x) * f x := by
      intro x
      simp only [u, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hM x, hg x,
        GlobalTheory.CharFormDeriv.rem]
      ring
    have hTu : T u = -I * T g := by
      simp only [u, map_sub, map_smul, hTM, smul_eq_mul]
      ring
    have hbound := GlobalTheory.CharFormDeriv.seminorm_rem_mul_le L f u ht0.ne'
      (by rw [abs_of_pos ht0]; exact ht1) hu
    have h1 : (s.sup (schwartzSeminormFamily ℂ V ℂ)) u ≤ t * ∑ m ∈ s, B m := by
      apply Seminorm.finset_sup_apply_le (mul_nonneg ht0.le hS)
      intro m hm
      have := hbound m.1 m.2
      rw [abs_of_pos ht0] at this
      calc schwartzSeminormFamily ℂ V ℂ m u = SchwartzMap.seminorm ℂ m.1 m.2 u := rfl
        _ ≤ t * B m := this
        _ ≤ t * ∑ m ∈ s, B m := by
          gcongr
          exact Finset.single_le_sum (fun i _ => hB0 i) hm
    have h2 := hC u
    have h3 : ‖T u‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) u := h2
    rw [hTu, norm_mul, norm_neg, Complex.norm_I, one_mul] at h3
    calc ‖T g‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) u := h3
      _ ≤ (C : ℝ) * (t * ∑ m ∈ s, B m) := by gcongr
      _ = t * ((C : ℝ) * ∑ m ∈ s, B m) := by ring
  have h0 : ‖T g‖ ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have hD : 0 < 2 * ((C : ℝ) * ∑ m ∈ s, B m + 1) := by positivity
    have ht := key (min 1 (‖T g‖ / (2 * ((C : ℝ) * ∑ m ∈ s, B m + 1))))
      (lt_min one_pos (div_pos hpos hD)) (min_le_left _ _)
    have hle : min 1 (‖T g‖ / (2 * ((C : ℝ) * ∑ m ∈ s, B m + 1))) * ((C : ℝ) * ∑ m ∈ s, B m)
        ≤ ‖T g‖ / 2 := by
      calc _ ≤ ‖T g‖ / (2 * ((C : ℝ) * ∑ m ∈ s, B m + 1)) * ((C : ℝ) * ∑ m ∈ s, B m) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hK
        _ ≤ ‖T g‖ / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hD (by norm_num)]
          nlinarith
    linarith
  exact norm_le_zero_iff.mp h0

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {κ' κ'' : Type} [Fintype κ']
  [Fintype κ'']

theorem arch_part (T : SchwartzMap (κ' ⊕ κ'' → W) ℂ →L[ℂ] ℂ)
    (hT : ∀ (L : (κ'' → W) →L[ℝ] ℝ) (f f' : SchwartzMap (κ' ⊕ κ'' → W) ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L (x ∘ Sum.inr) : ℂ)) * f x) → T f' = T f)
    (f : SchwartzMap (κ' ⊕ κ'' → W) ℂ) (hf : ∀ x : κ' ⊕ κ'' → W, x ∘ Sum.inr = 0 → f x = 0) : T f = 0 := by
  obtain ⟨n, L, hh, gg, hgg, hsum⟩ := param_hadamard f hf
  let P : (κ' ⊕ κ'' → W) →L[ℝ] (κ'' → W) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inr j)
  have hres : ∀ i, T (gg i) = 0 := by
    intro i
    refine kills_linear_mul T ((L i).comp P) ?_ (hh i) (gg i) ?_
    · intro t f₁ f₂ h
      apply hT (t • L i) f₁ f₂
      intro x
      rw [h x]
      rfl
    · intro x
      rw [hgg i x]
      rfl
  have hf' : f = ∑ i, gg i := by
    ext x
    rw [hsum x]
    simp
  rw [hf', map_sum]
  simp [hres]

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
