import Mathlib

set_option backward.isDefEq.respectTransparency false

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.GamU

variable {A C : Type*} [CommRing A] [CommRing C] (i : A →+* C) (t : A)
  {H N Q : Type*} [AddCommGroup H] [Module A H] [AddCommGroup N] [Module A N] [AddCommGroup Q]
  (β : H →ₗ[A] N) (κ : H →+ (Q →+ C))

def F (n : ℕ) (x : N → H) (y : N) (φ : Q) : C := Ring.inverse (i t ^ n) * κ (x y) φ

variable {i t β κ}

theorem key (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : IsUnit (i t))
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) {n : ℕ} {x : N → H} (hx : ∀ y, β (x y) = t ^ n • y)
    {c : A} {x' : H} {y : N} (h : β x' = c • y) (φ : Q) : κ x' φ = i c * F i t κ n x y φ := by
  obtain ⟨n₀, h₀⟩ := hinj
  have h1 : β (t ^ n • x' - c • x y) = 0 := by
    rw [map_sub, map_smul, map_smul, h, hx, smul_smul, smul_smul, mul_comm, sub_self]
  have h2 : κ (t ^ n₀ • (t ^ n • x' - c • x y)) φ = 0 := by rw [h₀ _ h1]; simp
  simp only [smul_sub, map_sub, AddMonoidHom.sub_apply, hlin, map_pow] at h2
  have h3 : i t ^ n * κ x' φ = i c * κ (x y) φ := by
    apply (ht.pow n₀).mul_left_cancel; linear_combination h2
  calc κ x' φ = Ring.inverse (i t ^ n) * (i t ^ n * κ x' φ) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ (ht.pow n), one_mul]
    _ = i c * F i t κ n x y φ := by rw [h3, F]; ring

def hom (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : IsUnit (i t))
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) (n : ℕ) (x : N → H) (hx : ∀ y, β (x y) = t ^ n • y) :
    N →+ (Q →+ C) :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun φ => F i t κ n x y φ) (by intro a b; simp [F, mul_add]))
    (by
      intro y y'
      ext φ
      have e := key hlin ht hinj hx (x' := x y + x y') (c := t ^ n) (y := y + y') (by simp [hx, smul_add]) φ
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      calc F i t κ n x (y + y') φ = Ring.inverse (i t ^ n) * (i (t ^ n) * F i t κ n x (y + y') φ) := by
            rw [← mul_assoc, map_pow, Ring.inverse_mul_cancel _ (ht.pow n), one_mul]
        _ = F i t κ n x y φ + F i t κ n x y' φ := by
            rw [← e, map_add, AddMonoidHom.add_apply, F, F, mul_add])

theorem hom_apply (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : IsUnit (i t))
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) (n : ℕ) (x : N → H) (hx : ∀ y, β (x y) = t ^ n • y) (y : N) (φ : Q) :
    hom hlin ht hinj n x hx y φ = F i t κ n x y φ := rfl

theorem hom_key (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : IsUnit (i t))
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) (n : ℕ) (x : N → H) (hx : ∀ y, β (x y) = t ^ n • y)
    {c : A} {x' : H} {y : N} (h : β x' = c • y) (φ : Q) : κ x' φ = i c * hom hlin ht hinj n x hx y φ :=
  key hlin ht hinj hx h φ

end CrystallineSemistableComparison.GamU

namespace CrystallineSemistableComparison.ExtV

variable {p : ℕ} [Fact p.Prime] {T Q C : Type*} [AddCommGroup T] [Module ℤ_[p] T] [AddCommGroup Q] [CommRing C]
  (ρ : ℚ_[p] →+* C) (g : T →+ (Q →+ C))

def ext (hg : ∀ (r : ℤ_[p]) (v : T) (f : Q), g (r • v) f = ρ (algebraMap ℤ_[p] ℚ_[p] r) * g v f) :
    ℚ_[p] ⊗[ℤ_[p]] T →+ (Q →+ C) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun z => AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun f => ρ z * g v f)
        (by intro a b; simp [mul_add])) (by intro a b; ext f; simp [mul_add]))
      (by intro a b; ext v f; simp [add_mul]))
    (by
      intro r z v
      ext f
      simp only [AddMonoidHom.mk'_apply, hg, Algebra.smul_def, map_mul]
      ring)

variable {ρ g}

theorem ext_tmul (hg : ∀ (r : ℤ_[p]) (v : T) (f : Q), g (r • v) f = ρ (algebraMap ℤ_[p] ℚ_[p] r) * g v f)
    (z : ℚ_[p]) (v : T) (f : Q) : ext ρ g hg (z ⊗ₜ v) f = ρ z * g v f := by
  simp [ext]

theorem ext_smul (hg : ∀ (r : ℤ_[p]) (v : T) (f : Q), g (r • v) f = ρ (algebraMap ℤ_[p] ℚ_[p] r) * g v f)
    (z : ℚ_[p]) (w : ℚ_[p] ⊗[ℤ_[p]] T) (f : Q) : ext ρ g hg (z • w) f = ρ z * ext ρ g hg w f := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rw [TensorProduct.smul_tmul', ext_tmul, ext_tmul, smul_eq_mul, map_mul, mul_assoc]
  | add u w hu hw => rw [smul_add, map_add, AddMonoidHom.add_apply, hu, hw, map_add, AddMonoidHom.add_apply, mul_add]

end CrystallineSemistableComparison.ExtV
