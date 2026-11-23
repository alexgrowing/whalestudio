import Mathlib
import Formalism.PeriodIntegrals.BetaLUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaLUniq

theorem agreeOnH : AgreeOnH := by
  intro E _ _ _ S Λ r T T' F F' F'' β₁ β₂ k hΛ hLF hLF'' hdim n' n'' hs1 hs2 x hx
  have hHp : finrank E (Hp Λ F F') + (2 * r + 2) = finrank E S.V := by
    have := finrank_orth_add S (UUE Λ F F')
    rw [n'.1] at this
    exact this
  have hle : ∀ β, Th Λ F F' F'' β ≤ Hp Λ F F' := by
    intro β y hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod] at hp
    exact hp.1.1.1
  have hTh : ∀ β, s0 Λ F F' F'' β k = 1 → Th Λ F F' F'' β = Hp Λ F F' := by
    intro β hs
    apply Submodule.eq_of_le_of_finrank_le (hle β)
    simp only [s0] at hs
    omega
  have hx1 : x ∈ Th Λ F F' F'' β₁ := by rw [hTh β₁ hs1]; exact hx
  have hx2 : x ∈ Th Λ F F' F'' β₂ := by rw [hTh β₂ hs2]; exact hx
  obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.mp hx1
  obtain ⟨q, hq, hq1⟩ := Submodule.mem_map.mp hx2
  simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at hp hq hp1 hq1
  subst hp1
  have e : p.2 = q.2 := by
    have hin : p.2 - q.2 ∈ UUE Λ F F'' ⊓ orth S (UUE Λ F F'') := by
      refine ⟨?_, ?_⟩
      · apply Xsp_le_UUE S Λ hΛ F F''
        have : p.2 - q.2 = (q.1 - q.2) - (p.1 - p.2) := by rw [hq1]; abel
        rw [this]
        exact (Xsp F).sub_mem hq.1.2 hp.1.2
      · exact (orth S (UUE Λ F F'')).sub_mem hp.1.1.2 hq.1.1.2
    rw [n''.2] at hin
    exact sub_eq_zero.mp ((Submodule.mem_bot E).mp hin)
  have : β₂ p.1 - β₁ p.1 = (β₂ q.1 - q.2) - (β₁ p.1 - p.2) := by rw [hq1, e]; abel
  rw [this]
  exact (Xsp F'').sub_mem hq.2 hp.2

end PI.UnitaryGroupMassFormula.BetaLUniq
