import Development.EtaleCohomology.KummerTheory.SHInsepPf

noncomputable section
open scoped TensorProduct

namespace LateralTheory.KummerTheory

section
variable {κ K : Type} [Field κ] [Field K] [Algebra κ K]

theorem shl_nontriv (B : Type) [CommRing B] [Nontrivial B] [Algebra κ B] : Nontrivial (B ⊗[κ] K) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_right κ B K (Algebra.linearMap κ B)
    (algebraMap κ B).injective

variable [IsPurelyInseparable κ K] {A : Type} [CommRing A] [Algebra κ A]

theorem shl_pow (q : ℕ) [ExpChar κ q] [ExpChar (A ⊗[κ] K) q] (y : A ⊗[κ] K) :
    ∃ n : ℕ, ∃ a : A, y ^ q ^ n = algebraMap A (A ⊗[κ] K) a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a k =>
    obtain ⟨n, c, hc⟩ := (isPurelyInseparable_iff_pow_mem κ q).1 inferInstance k
    refine ⟨n, c • a ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      Algebra.TensorProduct.algebraMap_apply]
    simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨n, a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := hy
    refine ⟨n + m, a ^ q ^ m + b ^ q ^ n, ?_⟩
    rw [add_pow_expChar_pow, map_add, map_pow, map_pow, ← ha, ← hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]

end

theorem SHInsepLoc_of : SHInsepLoc := by
  intro κ K A _ _ _ _ _ _ hA
  obtain ⟨hH, _⟩ := hA
  have : IsLocalRing A := hH.toIsLocalRing
  obtain ⟨q, hq⟩ := ExpChar.exists κ
  have : Nontrivial (A ⊗[κ] K) := shl_nontriv A
  have : ExpChar (A ⊗[κ] K) q := expChar_of_injective_algebraMap (algebraMap κ _).injective q
  have hqpos : ∀ n : ℕ, q ^ n ≠ 0 := fun n => pow_ne_zero _ (expChar_pos κ q).ne'

  have hm : ∀ a ∈ IsLocalRing.maximalIdeal A, ¬ IsUnit (algebraMap A (A ⊗[κ] K) a) := by
    intro a ha hu
    have : Nontrivial ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[κ] K) := shl_nontriv _
    let φ := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ κ (IsLocalRing.maximalIdeal A)) (AlgHom.id κ K)
    have h0 : φ (algebraMap A (A ⊗[κ] K) a) = 0 := by
      simp [φ, Algebra.TensorProduct.algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    have := hu.map φ
    rw [h0] at this
    exact not_isUnit_zero this
  have hkey : ∀ y : A ⊗[κ] K, ¬ IsUnit y →
      ∃ n : ℕ, ∃ a ∈ IsLocalRing.maximalIdeal A, y ^ q ^ n = algebraMap A (A ⊗[κ] K) a := by
    intro y hy
    obtain ⟨n, a, ha⟩ := shl_pow q y
    refine ⟨n, a, ?_, ha⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hy ((isUnit_pow_iff (hqpos n)).1 (ha ▸ hu.map _))
  refine IsLocalRing.of_nonunits_add ?_
  intro x y hx hy hxy
  obtain ⟨n, a, ha, hxa⟩ := hkey x hx
  obtain ⟨m, b, hb, hyb⟩ := hkey y hy
  apply hm (a ^ q ^ m + b ^ q ^ n)
  · exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ ha _ (Nat.pos_of_ne_zero (hqpos m)))
      (Ideal.pow_mem_of_mem _ hb _ (Nat.pos_of_ne_zero (hqpos n)))
  · have : (x + y) ^ q ^ (n + m) = algebraMap A (A ⊗[κ] K) (a ^ q ^ m + b ^ q ^ n) := by
      rw [add_pow_expChar_pow, map_add, map_pow, map_pow, ← hxa, ← hyb, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm m n]
    rw [← this]
    exact hxy.pow _

end LateralTheory.KummerTheory
