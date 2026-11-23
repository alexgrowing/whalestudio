import ReciprocityTheory.DualLattices.TangentPairingStatement

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

def ξmul {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker) :
    (R' : Type u) →ₗ[R₀] π.ker where
  toFun r := ⟨ξ * r, by
    rw [Submodule.restrictScalars_mem] at hξ ⊢
    exact Ideal.mul_mem_right r _ hξ⟩
  map_add' a b := by ext; simp [mul_add]
  map_smul' c r := by ext; simp

namespace BX

variable (B : BX R₀)

def ev {R' : LAlg R₀} (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h LinearMap.id v)

lemma evK_ξmul {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker)
    (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) :
    B.evK π h (TensorProduct.map LinearMap.id (ξmul π ξ hξ) v) = ξ * B.ev h v := by
  induction v using TensorProduct.induction_on with
  | zero => simp [evK, ev]
  | tmul g r =>
    simp only [evK, ev, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mul'_apply,
      Submodule.subtype_apply]
    show h g * (ξ * r) = ξ * (h g * r)
    ring
  | add x y hx hy =>
    simp only [evK, ev, map_add] at hx hy ⊢
    rw [hx, hy, mul_add]

end BX

def ThmALevelStatement (B : BX R₀) : Prop :=
  ∀ (R' R : LAlg R₀) (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker) (Dp : DualPair R)
    (N : ℕ) (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ})
    (hsq : ξ * ξ = 0),
    (∀ a, a * ξ = 0 → a ∈ Ideal.span {ξ}) → (N : (R' : Type u)) = 0 →
    ∀ (sh th : B.G R') (v w : B.gg ⊗[R₀] (R' : Type u)) (hs ht : B.gg →ₗ[R₀] R')
      (zh : (R' : Type u)ˣ) (z : (R : Type u)ˣ) (c : (R' : Type u)) (e₀ : ℤ),
      N • sh = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) (TensorProduct.map LinearMap.id (ξmul π ξ hξ) v) →
      N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) (TensorProduct.map LinearMap.id (ξmul π ξ hξ) w) →
      B.IsHeight Dp N (B.map π sh) (π.1.toLinearMap ∘ₗ hs) →
      B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ ht) →
      B.IsPairing N (B.map π sh) (B.map π th) z → Units.map (π.1 : R' →* R) zh = z →
      (zh : (R' : Type u)) ^ N = 1 + e₀ * c * ξ →
      π.1 (e₀ * c) = π.1 (B.ev ht v) - π.1 (B.ev hs w)

theorem thmA_level (B : BX R₀) (hB3 : TangentPairingStatement B) : ThmALevelStatement B := by
  intro R' R π ξ hξ Dp N hsurj hker hsq hann hN sh th v w hs ht zh z c e₀ hsh hth hhs hht hpair
    hzh hzN
  have h3 := hB3 R' R π ξ Dp N hsurj hker hsq hann hN sh th
    (TensorProduct.map LinearMap.id (ξmul π ξ hξ) v) (TensorProduct.map LinearMap.id (ξmul π ξ hξ) w)
    hs ht zh z hsh hth hhs hht hpair hzh
  rw [B.evK_ξmul, B.evK_ξmul, hzN] at h3
  have h4 : ((e₀ : (R' : Type u)) * c - (B.ev ht v - B.ev hs w)) * ξ = 0 := by
    linear_combination h3
  have h5 := hann _ h4
  rw [← hker, RingHom.mem_ker, map_sub, map_sub] at h5
  exact sub_eq_zero.mp h5

end ReciprocityTheory.PGsh
