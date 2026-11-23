import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem eq_refl_of_isometry_congMod : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[ℤ] X), (∀ x y, β (e x) (e y) = β x y) →
    ∀ N : ℕ, 3 ≤ N → (∀ x, CongMod N (e x) x) → e = LinearEquiv.refl ℤ X := by
  intro X _ _ _ β hpos e he N hN hc
  choose u hu using hc
  have hQ0 : ∀ x, 0 ≤ β x x := fun x => by
    by_cases h : x = 0
    · simp [h]
    · exact (hpos x h).le
  have hdec : ∀ x, x ≠ 0 → β (u x) (u x) < β x x := by
    intro x hx
    have h1 : 0 ≤ β (e x + x) (e x + x) := hQ0 _
    have h2 : β (e x - x) (e x - x) = (N : ℤ) * ((N : ℤ) * β (u x) (u x)) := by
      rw [show e x - x = N • u x by rw [hu x]; abel]
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, he x x] at h1 h2
    have hc := hpos x hx
    have hd := hQ0 (u x)
    have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul hN' hN' (by norm_num) (by omega)) hd]
  have hnil : ∀ n : ℕ, ∀ x, (β x x).toNat = n → ∃ k, u^[k] x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn
      by_cases hx : x = 0
      · exact ⟨0, by simpa using hx⟩
      · have hlt := hdec x hx
        have hd := hQ0 (u x)
        obtain ⟨k, hk⟩ := ih (β (u x) (u x)).toNat (by omega) (u x) rfl
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
  ext y
  by_contra hne
  have huy : u y ≠ 0 := fun h => hne (by rw [hu y, h]; simp)
  classical
  have hex : ∃ k, u^[k] y = 0 := hnil _ y rfl
  have hk : u^[Nat.find hex] y = 0 := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, u^[j] y ≠ 0 := fun j hj => Nat.find_min hex hj
  have hy0 : y ≠ 0 := fun h => hne (by simp [h])
  have hk2 : 2 ≤ Nat.find hex := by
    by_contra h
    interval_cases h' : Nat.find hex
    · exact hy0 (by simpa using hk)
    · exact huy (by simpa using hk)
  have hux : u (u^[Nat.find hex - 2] y) ≠ 0 := by
    rw [← Function.iterate_succ_apply' u]
    exact hmin _ (by omega)
  have huux : u (u (u^[Nat.find hex - 2] y)) = 0 := by
    rw [← Function.iterate_succ_apply' u, ← Function.iterate_succ_apply' u]
    rw [show (Nat.find hex - 2).succ.succ = Nat.find hex by omega]
    exact hk
  set x := u^[Nat.find hex - 2] y
  have key := he x (u x)
  rw [hu x, hu (u x), huux] at key
  simp only [smul_zero, add_zero, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at key
  have hp := hpos (u x) hux
  have hN0 : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  nlinarith [mul_pos hN0 hp]

end GlobalTheory.Poinc
