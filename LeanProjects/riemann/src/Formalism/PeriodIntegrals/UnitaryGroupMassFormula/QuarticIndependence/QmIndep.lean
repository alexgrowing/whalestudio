import Formalism.PeriodIntegrals.RTTIndependence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuarticIndependence.IndepC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuarticIndependence.IndepPoly

namespace PI.QmIndepW

open Complex

theorem scalar (z : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ) (Y Y' : ℂ) (hY : Y' ≠ Y + 1)
    (hz : ∀ (c : ℂ), c ≠ 0 → ∀ (β : ℂ) (n : ℤ),
      ∑ A : Fin 2 × Fin 2, ∑ B : Fin 2 × Fin 2,
        ((if A = (0, 0) then (Y - β) * (Y' - β) else if A = (0, 1) then Y' - β else if A = (1, 0) then Y - β + 1 else 1) *
          (if B = (0, 0) then (Y' + (β + n)) * (Y + (β + n)) else if B = (0, 1) then Y' + (β + n) - 1
            else if B = (1, 0) then Y + (β + n) else 1) *
          (((‖c‖ : ℂ) ^ (2 * β)) * c ^ n * (c ^ ((B.1 : ℕ) + (B.2 : ℕ)))⁻¹ * (star c ^ ((A.1 : ℕ) + (A.2 : ℕ)))⁻¹)) * z A B = 0) :
    ∀ A B, z A B = 0 := by
  apply indepPoly Y Y' hY z
  rintro β α ⟨n, rfl⟩
  have h9 := indepC
    ((Y - β) * (Y' - β) * ((Y' + (β + n)) * (Y + (β + n))) * z (0, 0) (0, 0))
    ((Y - β) * (Y' - β) * ((Y' + (β + n) - 1) * z (0, 0) (0, 1) + (Y + (β + n)) * z (0, 0) (1, 0)))
    ((Y - β) * (Y' - β) * z (0, 0) (1, 1))
    (((Y' - β) * z (0, 1) (0, 0) + (Y - β + 1) * z (1, 0) (0, 0)) * ((Y' + (β + n)) * (Y + (β + n))))
    ((Y' - β) * (Y' + (β + n) - 1) * z (0, 1) (0, 1) + (Y' - β) * (Y + (β + n)) * z (0, 1) (1, 0) +
      (Y - β + 1) * (Y' + (β + n) - 1) * z (1, 0) (0, 1) + (Y - β + 1) * (Y + (β + n)) * z (1, 0) (1, 0))
    ((Y' - β) * z (0, 1) (1, 1) + (Y - β + 1) * z (1, 0) (1, 1))
    ((Y' + (β + n)) * (Y + (β + n)) * z (1, 1) (0, 0))
    ((Y' + (β + n) - 1) * z (1, 1) (0, 1) + (Y + (β + n)) * z (1, 1) (1, 0))
    (z (1, 1) (1, 1)) (by
      intro c hc
      have h := hz c hc β n
      have hne : ((‖c‖ : ℂ) ^ (2 * β)) * c ^ n ≠ 0 := by
        refine mul_ne_zero ?_ (zpow_ne_zero n hc)
        rw [Ne, Complex.cpow_eq_zero_iff]
        simp [hc]
      refine (mul_eq_zero.mp ?_).resolve_left hne
      rw [← h]
      simp only [nine, Fintype.sum_prod_type, Fin.sum_univ_two, Prod.mk.injEq, Fin.isValue,
        Fin.val_zero, Fin.val_one, zero_ne_one, one_ne_zero, and_true, and_false, true_and, false_and,
        if_true, if_false, add_zero, zero_add]
      ring)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem qmIndep : PI.RTTIndependence := by
  intro V _ _ x Y Y' hY hx A B
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  refine scalar (fun A B => φ (x A B)) Y Y' hY (fun c hc β n => ?_) A B
  have h := congrArg φ (hx c hc β n)
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
  exact h

end PI.QmIndepW
