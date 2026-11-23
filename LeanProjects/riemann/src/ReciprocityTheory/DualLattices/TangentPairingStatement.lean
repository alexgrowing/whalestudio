import ReciprocityTheory.DualLattices.ModuliPointsState

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

def evK {R' R : LAlg R₀} (π : LHom R' R) (h : B.gg →ₗ[R₀] R') (V : B.gg ⊗[R₀] π.ker) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h π.ker.subtype V)

end BX

def TangentPairingStatement (B : BX R₀) : Prop :=
  ∀ (R' R : LAlg R₀) (π : LHom R' R) (ξ : (R' : Type u)) (Dp : DualPair R) (N : ℕ)
    (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0),
    (∀ a, a * ξ = 0 → a ∈ Ideal.span {ξ}) → (N : (R' : Type u)) = 0 →
    ∀ (sh th : B.G R') (Vs Vt : B.gg ⊗[R₀] π.ker) (hs ht : B.gg →ₗ[R₀] R')
      (zh : (R' : Type u)ˣ) (z : (R : Type u)ˣ),
      N • sh = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vs → N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vt →
      B.IsHeight Dp N (B.map π sh) (π.1.toLinearMap ∘ₗ hs) →
      B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ ht) →
      B.IsPairing N (B.map π sh) (B.map π th) z → Units.map (π.1 : R' →* R) zh = z →
      (zh : (R' : Type u)) ^ N = 1 + (B.evK π ht Vs - B.evK π hs Vt)

end ReciprocityTheory.PGsh
