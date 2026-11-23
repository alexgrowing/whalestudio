import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel NNReal

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem inner_eq (ψ : AddChar F Circle) (hψ : IsStd ψ) (y c : F) (hy : y ≠ 0) :
    ∫ x, (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * (c + x)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ =
      (ψ c : ℂ) * (if ord y ≤ 0 then ((residueCard F : ℂ)) ^ (ord y) else 0) := by
  have h1 : ∫ x, (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * (c + x)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ
      = ∫ x, (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * x) * (ψ (-(x - c)) : ℂ) ∂selfDualMeasure ψ := by
    rw [← integral_add_left_eq_self
      (fun x => (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * x) * (ψ (-(x - c)) : ℂ)) c]
    simp only [add_sub_cancel_left]
  rw [h1]
  have h2 : ∀ x, (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * x) * (ψ (-(x - c)) : ℂ)
      = (ψ c : ℂ) * ((𝒪[F] : Set F).indicator (fun z => (ψ.mulShift (-y⁻¹) z : ℂ)) (y * x)) := by
    intro x
    by_cases hx : y * x ∈ (𝒪[F] : Set F)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, AddChar.mulShift_apply]
      have : -(x - c) = c + -y⁻¹ * (y * x) := by field_simp; ring
      rw [this, AddChar.map_add_eq_mul]
      simp
    · simp [Set.indicator_of_notMem hx]
  simp_rw [h2]
  rw [integral_const_mul, integral_comp_mul_left (selfDualMeasure ψ) hy
    (fun z => (𝒪[F] : Set F).indicator (fun z => (ψ.mulShift (-y⁻¹) z : ℂ)) z)]
  rw [integral_indicator (by rw [← coe_valBall_zero]; exact measurableSet_valBall 0),
    ← coe_valBall_zero, integral_valBall_char]
  have hcond : addCharConductor ψ = 0 := hψ.2.2
  have hy' : -y⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hy)
  have htriv : IsTrivialOn (ψ.mulShift (-y⁻¹)) 0 ↔ ord y ≤ 0 := by
    rw [isTrivialOn_mulShift_iff hy', isTrivialOn_iff hψ.1 hψ.2.1, hcond, ord_neg_eq, ord_inv hy]
    omega
  have hvol : (selfDualMeasure ψ).real (valBall F 0) = 1 := by
    rw [selfDualMeasure_real_valBall_zero, hcond]; simp
  rw [modulus_of_ne_zero hy]
  by_cases h : ord y ≤ 0
  · rw [if_pos (htriv.2 h), if_pos h, hvol]
    simp only [NNReal.coe_zpow, NNReal.coe_natCast, Complex.ofReal_one, smul_eq_mul]
    rw [Complex.real_smul]
    push_cast
    rw [_root_.zpow_neg, inv_inv]
    ring
  · rw [if_neg (fun h' => h (htriv.1 h')), if_neg h]
    simp

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2
