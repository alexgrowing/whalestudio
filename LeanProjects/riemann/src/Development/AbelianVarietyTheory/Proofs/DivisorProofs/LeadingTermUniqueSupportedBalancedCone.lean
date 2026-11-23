import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThreeStatement

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem leadingTerm_unique : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X →
    ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a →
    ∀ (β : LinearMap.BilinForm ℤ X) (k : ℕ) (c : Fin r → ℕ), 0 < k → (∀ j, 0 < c j) → k • β = ∑ j, c j • γ j →
    (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[O] X) (N : ℕ), 3 ≤ N → (∀ x, CongMod N (e x) x) →
    d * φ.evalZ β = (∑ i, β (e (a i)) (e (a i)) : ℤ) → ∀ x, e x = x := by
  intro O _ bar φ d X _ _ _ _ _ _ hF r m γ a hγ hS β k c hk hc hβ hpos e N hN he hd
  have hkβ : ∀ y z, (k : ℤ) * β y z = ∑ j, (c j : ℤ) * γ j y z := fun y z => by
    have := LinearMap.congr_fun₂ hβ y z
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hbal : β ∈ balForms bar X := by
    refine ⟨fun y z => mul_left_cancel₀ hk0 ?_, fun o y z => mul_left_cancel₀ hk0 ?_⟩
    · rw [hkβ, hkβ]; exact Finset.sum_congr rfl fun j _ => by rw [(hγ.mem j).1]
    · rw [hkβ, hkβ]; exact Finset.sum_congr rfl fun j _ => by rw [(hγ.mem j).2]
  have hbal' : pull e.toLinearMap β ∈ balForms bar X := pull_mem _ hbal
  have hnn' : ∀ y, 0 ≤ pull e.toLinearMap β y y := fun y => by
    rw [pull_apply]
    by_cases h0 : e.toLinearMap y = 0
    · rw [h0]; simp
    · exact (hpos _ h0).le
  obtain ⟨k', c', hk', hβ'⟩ := hS.only _ hbal' hnn' (by rw [evalZ_pull φ e.surjective]; exact hd)
  have hsum : ∑ j, (k' * c j) • pull e.toLinearMap (γ j) = ∑ j, (k * c' j) • γ j := by
    refine LinearMap.ext₂ fun y z => ?_
    have h1 := hkβ (e y) (e z)
    have h2 := LinearMap.congr_fun₂ hβ' y z
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, nsmul_eq_mul, LinearEquiv.coe_coe] at h1 h2 ⊢
    have e1 : ∑ j, ((k' * c j : ℕ) : ℤ) * γ j (e y) (e z) = k' * ∑ j, (c j : ℤ) * γ j (e y) (e z) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    have e2 : ∑ j, ((k * c' j : ℕ) : ℤ) * γ j y z = k * ∑ j, (c' j : ℤ) * γ j y z := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [e1, e2, ← h1, ← h2]; ring
  have hγe : IsCone bar φ fun j => pull e.toLinearMap (γ j) := hγ.pull_equiv e
  choose σ hσ using GlobalTheory.T.smoothCone_face_of_interior_common_point O bar φ X hF r r _ γ hγe hγ (fun j => k' * c j) (fun j => k * c' j)
    (fun j => Nat.mul_pos hk' (hc j)) hsum
  have hσinj : Function.Injective σ := fun i j hij => hγe.injective (by simp only [hσ, hij])
  let σe := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have hG : ∀ y z, (∑ j, γ j) (e y) (e z) = (∑ j, γ j) y z := by
    intro y z
    simp only [LinearMap.sum_apply]
    calc ∑ j, γ j (e y) (e z) = ∑ j, γ (σe j) y z :=
          Finset.sum_congr rfl fun j _ => LinearMap.congr_fun₂ (hσ j) y z
      _ = ∑ j, γ j y z := σe.sum_comp (fun j => γ j y z)
  have hGpos : ∀ x, x ≠ 0 → 0 < (∑ j, γ j) x x := by
    intro x hx
    have h2 : 0 < (k : ℤ) * β x x := mul_pos (by exact_mod_cast hk) (hpos x hx)
    rw [hkβ] at h2
    obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (show ∑ j : Fin r, (0 : ℤ) < _ by simpa using h2)
    have hj' : 0 < γ j x x := pos_of_mul_pos_right hj (by positivity)
    simp only [LinearMap.sum_apply]
    exact hj'.trans_le (Finset.single_le_sum (fun i _ => hγ.nonneg i x) (Finset.mem_univ j))
  have key := GlobalTheory.T.isometry_eq_refl_of_congr_mod_ge_three X (∑ j, γ j) hGpos e.toAddEquiv.toIntLinearEquiv (fun y z => hG y z) N hN he
  intro x
  simpa using LinearEquiv.congr_fun key x

end GlobalTheory.Poinc
