import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.RatIntOfIntegral

noncomputable section

namespace PI.GoodTwo.AlgebraicValuationTrichotomy

open NumberField QuadraticAlgebra

section
variable (m : ℕ) [Fact (∀ r : ℚ, r ^ 2 ≠ -(m : ℚ) + 1 * r)]

def mkO (x y : ℤ) : 𝓞 (Kq m) :=
  ⟨⟨x, y⟩, by rw [mem_integralClosure_iff]; convert isIntegral_mk m x y⟩

@[simp] theorem algebraMap_mkO (x y : ℤ) :
    algebraMap (𝓞 (Kq m)) (Kq m) (mkO m x y) = ⟨x, y⟩ := rfl

theorem mkO_inj {a b c e : ℤ} (h : mkO m a b = mkO m c e) : a = c ∧ b = e := by
  have h' := congrArg (algebraMap (𝓞 (Kq m)) (Kq m)) h
  simp only [algebraMap_mkO] at h'
  obtain ⟨h1, h2⟩ := QuadraticAlgebra.mk.inj h'
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem mkO_mul (a b c e : ℤ) :
    mkO m a b * mkO m c e = mkO m (a * c - m * b * e) (a * e + b * c + b * e) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (Kq m)) (Kq m)
  rw [map_mul, algebraMap_mkO, algebraMap_mkO, algebraMap_mkO]
  ext <;> simp <;> push_cast <;> ring

theorem mkO_add (a b c e : ℤ) : mkO m a b + mkO m c e = mkO m (a + c) (b + e) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (Kq m)) (Kq m)
  rw [map_add, algebraMap_mkO, algebraMap_mkO, algebraMap_mkO]
  ext <;> simp

theorem mkO_sub (a b c e : ℤ) : mkO m a b - mkO m c e = mkO m (a - c) (b - e) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (Kq m)) (Kq m)
  rw [map_sub, algebraMap_mkO, algebraMap_mkO, algebraMap_mkO]
  ext <;> simp

theorem one_O : (1 : 𝓞 (Kq m)) = mkO m 1 0 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (Kq m)) (Kq m)
  rw [map_one, algebraMap_mkO]
  ext <;> simp

theorem two_O : (2 : 𝓞 (Kq m)) = mkO m 2 0 := by
  rw [show (2 : 𝓞 (Kq m)) = 1 + 1 by norm_num, one_O, mkO_add]
  norm_num

theorem pow_two_O (h : ℕ) : (2 : 𝓞 (Kq m)) ^ h = mkO m (2 ^ h) 0 := by
  induction h with
  | zero => simp [one_O]
  | succ k ih =>
    rw [pow_succ, ih, two_O, mkO_mul]
    congr 1 <;> ring

theorem star_O (x y : ℤ) :
    RingOfIntegers.mapRingHom (starRingEnd (Kq m)) (mkO m x y) = mkO m (x + y) (-y) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (Kq m)) (Kq m)
  show (starRingEnd (Kq m)) (algebraMap (𝓞 (Kq m)) (Kq m) (mkO m x y)) = _
  rw [algebraMap_mkO, algebraMap_mkO, starRingEnd_apply, QuadraticAlgebra.star_mk]
  ext <;> simp

theorem repr_O (d : ℕ) (hd : Squarefree d) (hdm : d + 1 = 4 * m) (α : 𝓞 (Kq m)) :
    ∃ x y : ℤ, α = mkO m x y := by
  obtain ⟨x, y, h⟩ := repr_int m d hd hdm _ (RingOfIntegers.isIntegral_coe α)
  exact ⟨x, y, FaithfulSMul.algebraMap_injective (𝓞 (Kq m)) (Kq m) (by rw [algebraMap_mkO]; exact h)⟩

theorem int_dvd (d : ℕ) (hd : Squarefree d) (hdm : d + 1 = 4 * m) {a b : ℤ}
    (h : mkO m a 0 ∣ mkO m b 0) : a ∣ b := by
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨x, y, rfl⟩ := repr_O m d hd hdm γ
  rw [mkO_mul] at hγ
  obtain ⟨h1, -⟩ := mkO_inj m hγ
  exact ⟨x, by rw [h1]; ring⟩

end

end PI.GoodTwo.AlgebraicValuationTrichotomy
