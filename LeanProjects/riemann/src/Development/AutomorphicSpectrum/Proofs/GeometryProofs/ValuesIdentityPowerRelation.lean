import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem values_units_identity {G : Type*} [CommGroup G] (m N : ℕ)
    (Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz : G)
    (h3 : A = bo * (bz ^ (N ^ 2))⁻¹ * Wy)
    (h4 : B = bo * (bo ^ (N ^ 2))⁻¹ * Wo)
    (h5 : R = bo * R')
    (h7 : Wkz * up ^ ((N * m) ^ 2) * (A ^ ((m ^ 2) ^ 2))⁻¹ =
      Wkx * u0 ^ ((N * m) ^ 2) * (B ^ ((m ^ 2) ^ 2))⁻¹)
    (h8 : Wkx * Wm1 ^ (N ^ 2) = Wk1 * Wmx ^ (N ^ 2))
    (h9 : u0 = e0 * (R ^ (m ^ 2))⁻¹)
    (h10 : e0 ^ (m ^ 2) * Wmx * Wm1⁻¹ * (R ^ (m ^ 2))⁻¹ = 1) :
    (Wo * R' ^ (N ^ 2)) ^ ((m ^ 2) ^ 2) * bz ^ (m ^ 2 * (N * m) ^ 2) =
      Wk1 * R ^ ((N * m) ^ 2) * Wkz⁻¹ * (up ^ ((N * m) ^ 2))⁻¹ * Wy ^ ((m ^ 2) ^ 2) := by
  apply Additive.ofMul.injective
  have e3 := congrArg Additive.ofMul h3
  have e4 := congrArg Additive.ofMul h4
  have e5 := congrArg Additive.ofMul h5
  have e7 := congrArg Additive.ofMul h7
  have e8 := congrArg Additive.ofMul h8
  have e9 := congrArg Additive.ofMul h9
  have e10 := congrArg Additive.ofMul h10
  first
    | (simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, ← natCast_zsmul, Nat.cast_pow,
          Nat.cast_mul] at e3 e4 e5 e7 e8 e9 e10 ⊢
       linear_combination (norm := module) e7 + (((m : ℤ) ^ 2) ^ 2) • e3
         - (((m : ℤ) ^ 2) ^ 2) • e4 - ((N : ℤ) ^ 2 * ((m : ℤ) ^ 2) ^ 2) • e5
         + ((N : ℤ) ^ 2 * (m : ℤ) ^ 2) • e9 + e8 + ((N : ℤ) ^ 2) • e10)
    | (simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e3 e4 e5 e7 e8 e9 e10 ⊢
       linear_combination (norm := module) e7 + (((m : ℤ) ^ 2) ^ 2) • e3
         - (((m : ℤ) ^ 2) ^ 2) • e4 - ((N : ℤ) ^ 2 * ((m : ℤ) ^ 2) ^ 2) • e5
         + ((N : ℤ) ^ 2 * (m : ℤ) ^ 2) • e9 + e8 + ((N : ℤ) ^ 2) • e10)

theorem values_cancel_of_unit_identity {C : Type*} [CommRing C] (T2 T' s t D : C) (X Z Y V c K : Cˣ)
    (a : T2 * (X : C) = s * (Y : C)) (b : (Z : C) * s = D * (t * (V : C)))
    (c1 : T' * (c : C) = t * (K : C)) (hU : X * Z = c * K⁻¹ * V * Y) :
    T2 = D * T' := by
  have hU' : (X : C) * (Z : C) = (c : C) * ((K⁻¹ : Cˣ) : C) * (V : C) * (Y : C) := by
    simpa only [Units.val_mul] using congrArg Units.val hU
  have hK : ((K⁻¹ : Cˣ) : C) * (K : C) = 1 := Units.inv_mul K
  refine (Units.mul_left_inj (X * Z)).mp ?_
  rw [Units.val_mul]
  linear_combination (Z : C) * a + (Y : C) * b - D * T' * hU'
    - D * (V : C) * (Y : C) * ((K⁻¹ : Cˣ) : C) * c1 - D * t * (V : C) * (Y : C) * hK

theorem values_identity_units : ∀ {C : Type} [CommRing C] (m N : ℕ) (T T' th sv d : C) (Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz : Cˣ), T' * ((Wk1 : C) * (R : C) ^ ((N * m) ^ 2)) = th ^ ((N * m) ^ 2) * (Wkz : C) → T * ((Wo : C) * (R' : C) ^ (N ^ 2)) ^ (m ^ 2) = sv ^ (N ^ 2) * (Wy : C) ^ (m ^ 2) → A = bo * (bz ^ (N ^ 2))⁻¹ * Wy → B = bo * (bo ^ (N ^ 2))⁻¹ * Wo → R = bo * R' → ((bz ^ (m ^ 2) : Cˣ) : C) * sv = d * (th * ((up⁻¹ : Cˣ) : C)) → Wkz * up ^ ((N * m) ^ 2) * (A ^ ((m ^ 2) ^ 2))⁻¹ = Wkx * u0 ^ ((N * m) ^ 2) * (B ^ ((m ^ 2) ^ 2))⁻¹ → Wkx * Wm1 ^ (N ^ 2) = Wk1 * Wmx ^ (N ^ 2) → u0 = e0 * (R ^ (m ^ 2))⁻¹ → e0 ^ (m ^ 2) * Wmx * Wm1⁻¹ * (R ^ (m ^ 2))⁻¹ = 1 → T ^ (m ^ 2) = d ^ ((N * m) ^ 2) * T' := by
  intro C _ m N T T' th sv d Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz e1 e2 h3 h4 h5 e6 h7
    h8 h9 h10
  have hU := GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_units_identity m N Wk1 Wkz Wkx Wm1 Wmx A B up u0
    e0 R R' Wo Wy bo bz h3 h4 h5 h7 h8 h9 h10
  rw [← inv_pow] at hU
  have e2' : (T * ((Wo : C) * (R' : C) ^ (N ^ 2)) ^ (m ^ 2)) ^ (m ^ 2) =
      (sv ^ (N ^ 2) * (Wy : C) ^ (m ^ 2)) ^ (m ^ 2) := by rw [e2]
  have e6' : (((bz ^ (m ^ 2) : Cˣ) : C) * sv) ^ ((N * m) ^ 2) =
      (d * (th * ((up⁻¹ : Cˣ) : C))) ^ ((N * m) ^ 2) := by rw [e6]
  refine GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_cancel_of_unit_identity (T ^ (m ^ 2)) T' (sv ^ ((N * m) ^ 2))
    (th ^ ((N * m) ^ 2)) (d ^ ((N * m) ^ 2)) ((Wo * R' ^ (N ^ 2)) ^ ((m ^ 2) ^ 2))
    (bz ^ (m ^ 2 * (N * m) ^ 2)) (Wy ^ ((m ^ 2) ^ 2)) (up⁻¹ ^ ((N * m) ^ 2))
    (Wk1 * R ^ ((N * m) ^ 2)) Wkz ?_ ?_ ?_ hU
  · push_cast at e2' ⊢
    linear_combination e2'
  · push_cast at e6' ⊢
    linear_combination e6'
  · push_cast
    exact e1

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
