import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem vOp_hasSum (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (hq : 0 < q)
    (hf : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun m => (if q ∣ m then a (m / q) else 0) • Function.Periodic.qParam 1 τ ^ m)
      (GlobalTheory.Hk.vOp q f τ) := by
  have him : 0 < ((q : ℂ) * (τ : ℂ)).im := by
    have : ((q : ℂ) * (τ : ℂ)).im = (q : ℝ) * τ.im := by simp
    rw [this]; exact mul_pos (by exact_mod_cast hq) τ.im_pos
  set τ' : ℍ := ofComplex ((q : ℂ) * τ) with hτ'
  have hc : (τ' : ℂ) = (q : ℂ) * τ := by
    rw [hτ', ofComplex_apply_of_im_pos him]
  have hqp : Function.Periodic.qParam 1 (τ' : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ q := by
    simp only [Function.Periodic.qParam, hc, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have h1 := hf τ'
  unfold vOp
  rw [← hτ']
  refine (Function.Injective.hasSum_iff (g := fun m : ℕ => q * m)
    (fun x y h => Nat.eq_of_mul_eq_mul_left hq h) ?_).mp ?_
  · intro x hx
    have : ¬ q ∣ x := by
      rintro ⟨c, rfl⟩; exact hx ⟨c, rfl⟩
    simp [this]
  · convert h1 using 1
    funext m
    simp only [Function.comp, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hq, hqp, ← pow_mul]

end GlobalTheory.Hk
