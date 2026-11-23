import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem rad_mul_levi_apply {β : Fin n → ℕ} {u p : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β) {i j : Fin n}
    (hij : β j ≤ β i) : mat (u * p) i j = mat p i j := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hu i i le_rfl, Matrix.one_apply_eq, one_mul]
  · intro l _ hl
    rcases le_or_gt (β l) (β i) with h1 | h1
    · rw [hu i l h1, Matrix.one_apply_ne hl.symm, zero_mul]
    · rw [hp l j (by omega), mul_zero]
  · simp

theorem rad_levi_rad_apply {β : Fin n → ℕ} {u p u' : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β)
    (hu' : u' ∈ radU σ β) {i j : Fin n} (hij : β j ≤ β i) : mat (u * p * u') i j = mat p i j := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hu' j j le_rfl, Matrix.one_apply_eq, mul_one]
    exact rad_mul_levi_apply hu hp hij
  · intro l _ hl
    rcases le_or_gt (β j) (β l) with h1 | h1
    · rw [hu' l j h1, Matrix.one_apply_ne hl, mul_zero]
    · rw [rad_mul_levi_apply hu hp (by omega), hp i l (by omega), zero_mul]
  · simp

variable {N : ℕ}

theorem levi_mul_zero {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) : mat (x * y) 0 0 = mat x 0 0 * mat y 0 0 := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero, hx 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
    add_zero]
  intro j _
  rw [hx 0 (mid j) (by simp), zero_mul]

theorem levi_mul_last {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) :
    mat (x * y) (Fin.last (N + 1)) (Fin.last (N + 1)) =
      mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * mat y (Fin.last (N + 1)) (Fin.last (N + 1)) := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero, hx (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
    zero_add]
  intro j _
  rw [hx (Fin.last (N + 1)) (mid j) (by simp), zero_mul]

theorem levi_mul_mid {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (i j : Fin N) :
    mat (x * y) (mid i) (mid j) = ∑ k, mat x (mid i) (mid k) * mat y (mid k) (mid j) := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, hx (mid i) 0 (by simp), hx (mid i) (Fin.last (N + 1)) (by simp)]
  simp

end

theorem cosetInj : CosetInj := by
  intro L _ _ ϖ σ q N hU a a' g₀ g₀' m m' hm hm' u hu u' hu' hk
  obtain ⟨-, hσ, hσϖ, hϖ, -, -, -⟩ := hU
  obtain ⟨hl, h0, h1, h2⟩ := hm
  obtain ⟨hl', h0', h1', h2'⟩ := hm'
  have hli : m⁻¹ ∈ leviU σ (blk N) := inv_mem hl
  have hp : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hli hl'
  have e : (m * u)⁻¹ * (m' * u') = u⁻¹ * (m⁻¹ * m') * u' := by group
  rw [e] at hk
  have hint : ∀ i j, blk N j ≤ blk N i → mat (m⁻¹ * m') i j ∈ intL L := fun i j hij => by
    rw [← rad_levi_rad_apply (inv_mem hu) hp hu' hij]
    exact (mem_KU_iff hσ _).1 hk i j
  have e0 : mat (m⁻¹ * m') 0 0 = ϖ ^ (a' - a) := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_zero hli, mat_inv_apply, Fin.rev_zero, h1, h0', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have e1 : mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (a - a') := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_last hli, mat_inv_apply, Fin.rev_last, h0, h1', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have hv0 : 0 < Valued.v ϖ := by rw [hϖ]; exact WithZero.zero_lt_coe _
  have hv1 : Valued.v ϖ < 1 := by
    rw [hϖ]
    exact WithZero.coe_lt_one.2 (by decide)
  have i0 : Valued.v ϖ ^ (a' - a) ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') 0 0) ≤ 1 := hint 0 0 le_rfl
    rwa [e0, map_zpow₀] at this
  have i1 : Valued.v ϖ ^ (a - a') ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1))) ≤ 1 :=
      hint _ _ (le_refl (blk N (Fin.last (N + 1))))
    rwa [e1, map_zpow₀] at this
  rw [zpow_le_one_iff_right_of_lt_one₀ hv0 hv1] at i0 i1
  refine ⟨by omega, (mem_KU_iff hσ _).2 fun i j => ?_⟩
  have := hint (mid i) (mid j) (by simp)
  have e2 : ∀ i j, mat m⁻¹ (mid i) (mid j) = mat g₀⁻¹ i j := fun i j => by
    rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, h2]
  rw [levi_mul_mid hli] at this
  simp only [e2, h2'] at this
  rw [mat_mul, Matrix.mul_apply]
  exact this

end GlobalTheory.CompanionTheory.InertZeta

end
