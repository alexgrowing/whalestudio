import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightC

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

theorem sL_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n, ‖sL Q y‖ ≤ C * ‖F0 p q e y‖ := by
  have hK := isCompact_KR (n := n)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hL.cont Q).continuousOn
  have hne : ((KR n : Subgroup (GR n)) : Set (GR n)).Nonempty := ⟨1, (KR n).one_mem⟩
  obtain ⟨k0, -, hmin⟩ := hK.exists_isMinOn hne (continuous_weight_factor (n := n) hD p q e).norm.continuousOn
  have hδ : 0 < ‖F0 p q e k0‖ := norm_pos_iff.mpr (weight_factor_ne_zero hD p q e k0)
  refine ⟨max B 0 / ‖F0 p q e k0‖, div_nonneg (le_max_right _ _) hδ.le, fun y => ?_⟩
  obtain ⟨u, k, hu, hk, rfl⟩ := hI n y
  have hmk : ‖F0 p q e k0‖ ≤ ‖F0 p q e k‖ := hmin hk
  rw [hL.law Q u k hu, ((hM n p q e).1 u k hk).1, norm_mul, norm_mul]
  have h1 : ‖sL Q k‖ ≤ max B 0 := (hB k hk).trans (le_max_left _ _)
  have h2 : max B 0 ≤ max B 0 / ‖F0 p q e k0‖ * ‖F0 p q e k‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    exact mul_le_mul_of_nonneg_left hmk (le_max_right _ _)
  calc ‖F0 p q e u‖ * ‖sL Q k‖ ≤ ‖F0 p q e u‖ * (max B 0 / ‖F0 p q e k0‖ * ‖F0 p q e k‖) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
    _ = max B 0 / ‖F0 p q e k0‖ * (‖F0 p q e u‖ * ‖F0 p q e k‖) := by ring

theorem rpow_le_add {a x₁ x₂ s : ℝ} (ha : 0 < a) (h₁ : x₁ ≤ s) (h₂ : s ≤ x₂) : a ^ s ≤ a ^ x₁ + a ^ x₂ := by
  rcases le_total 1 a with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h h₂
    have := Real.rpow_nonneg ha.le x₁
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ha h h₁
    have := Real.rpow_nonneg ha.le x₂
    linarith

section Glob

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem Ht_pos (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (x : G) : 0 < (Ht x : ℝ) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).1]
  exact mul_pos hr (hLoc_pos hD y)

theorem sec_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G, ‖sec Q x‖ ≤ C * ‖sec 1 x‖ := by
  obtain ⟨C, hC0, hC⟩ := PositivityTheory.Rg.Sw.AbsSt.FarK.sL_bound hI hM hD hL Q
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨x0, y, S, r, -, hx, hy⟩ := hG.split x
  subst hx
  rw [(hy y).2 Q, (hy y).2 1, hL.vac y, norm_mul, norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg S)

theorem norm_hz (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (z : ℂ) (Q : PX m n) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ = (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ := by
  have hpos := PositivityTheory.Rg.Sw.AbsSt.FarK.Ht_pos hD hG x
  simp only [hz, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re]

end Glob

end PositivityTheory.Rg.Sw.AbsSt.FarK
