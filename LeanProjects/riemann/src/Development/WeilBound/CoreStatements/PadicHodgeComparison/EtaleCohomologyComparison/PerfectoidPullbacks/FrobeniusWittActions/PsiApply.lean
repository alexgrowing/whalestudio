import Mathlib

set_option backward.isDefEq.respectTransparency false

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Pb.Psi

variable {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
  {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type*} [AddCommGroup L] [Module W L]

def T (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) : A ⊗[W] L →+ C₀ :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun y => c a * k (f (1 ⊗ₜ y))
          map_zero' := by simp
          map_add' := fun y y' => by rw [tmul_add, map_add, map_add, mul_add] }
      map_zero' := by ext; simp
      map_add' := fun a a' => by ext; simp [add_mul] }
    (fun w a y => by
      change c (w • a) * k (f (1 ⊗ₜ y)) = c a * k (f (1 ⊗ₜ (w • y)))
      have e : (1 : K₀) ⊗ₜ[W] (w • y) = (algebraMap W K₀ w) • ((1 : K₀) ⊗ₜ[W] y) := by
        rw [tmul_smul, algebraMap_smul]
      rw [e, Algebra.smul_def w a, LinearMap.map_smul, smul_eq_mul, map_mul, map_mul, hk]
      ring)

theorem T_tmul (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (y : L) : T c k hk f (a ⊗ₜ y) = c a * k (f (1 ⊗ₜ y)) := rfl

theorem T_add (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    (f g : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) : T c k hk (f + g) z = T c k hk f z + T c k hk g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp only [T_tmul, LinearMap.add_apply, map_add, mul_add]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']; ring

def psi (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) (u : C₀)
    {Λ : Type*} [AddCommGroup Λ] (α : Λ →+ A ⊗[W] L) : Λ →+ (Module.Dual K₀ (K₀ ⊗[W] L) →+ C₀) where
  toFun x :=
    { toFun := fun f => u * T c k hk f (α x)
      map_zero' := by
        have : T c k hk (0 : Module.Dual K₀ (K₀ ⊗[W] L)) (α x) = 0 := by
          have h := T_add c k hk 0 0 (α x); simp only [add_zero] at h; exact left_eq_add.1 h
        rw [this, mul_zero]
      map_add' := fun f g => by rw [T_add, mul_add] }
  map_zero' := by ext f; simp
  map_add' x y := by ext f; simp [mul_add]

theorem psi_apply (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) (u : C₀)
    {Λ : Type*} [AddCommGroup Λ] (α : Λ →+ A ⊗[W] L) (x : Λ) (f : Module.Dual K₀ (K₀ ⊗[W] L)) :
    psi c k hk u α x f = u * T c k hk f (α x) := rfl

end CrystallineSemistableComparison.Pb.Psi
