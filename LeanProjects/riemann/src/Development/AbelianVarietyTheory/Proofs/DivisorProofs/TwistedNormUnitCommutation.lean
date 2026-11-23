import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory

theorem twisted_norm_local_step : ∀ {A K : Type} [Ring A] [CommRing K] [Algebra K A] (σ : A →+* Aᵐᵒᵖ), (∀ x, (σ (σ x).unop).unop = x) →
    ∀ (β Y k z m : Aˣ) (a : A) (lam s : Kˣ), (σ (β : A)).unop = β →
    (Y : A) * β * (σ (Y : A)).unop = algebraMap K A s * β → Commute a Y →
    (k : A) * (a * β) * (σ (k : A)).unop = algebraMap K A lam → k⁻¹ = z * m → Commute (z : A) Y →
    (∀ m' : Aˣ, (m' : A) = m * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) → Commute (m' : A) Y →
      (β : A) * (σ (m' : A)).unop * ((β⁻¹ : Aˣ) : A) = m' →
      ∃ v : Aˣ, Commute (v : A) Y ∧ (m' : A) = v * ((β : A) * (σ (v : A)).unop * ((β⁻¹ : Aˣ) : A))) →
    ∃ z' : Aˣ, Commute (z' : A) Y ∧ a = algebraMap K A lam * ((z' : A) * β * (σ (z' : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
  intro A K _ _ _ σ hσ β Y k z m a lam s hβ hY haY hk hkz hzY H
  have shmul : ∀ x y : A, (σ (x * y)).unop = (σ y).unop * (σ x).unop := fun x y => by
    rw [map_mul, MulOpposite.unop_mul]
  have shinv : ∀ u : Aˣ, (σ ((u⁻¹ : Aˣ) : A)).unop * (σ (u : A)).unop = 1 := fun u => by
    rw [← shmul, Units.mul_inv, map_one, MulOpposite.unop_one]
  have shinv' : ∀ u : Aˣ, (σ (u : A)).unop * (σ ((u⁻¹ : Aˣ) : A)).unop = 1 := fun u => by
    rw [← shmul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have shc : ∀ (u : Aˣ) (x : A), (σ (u : A)).unop * ((σ ((u⁻¹ : Aˣ) : A)).unop * x) = x := by
    intro u x; rw [← mul_assoc, shinv', one_mul]

  have hτY : (β : A) * (σ (Y : A)).unop * ((β⁻¹ : Aˣ) : A) = algebraMap K A s * ((Y⁻¹ : Aˣ) : A) := by
    have h := congrArg (fun x => ((Y⁻¹ : Aˣ) : A) * x * ((β⁻¹ : Aˣ) : A)) hY
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one] at h
    rw [mul_assoc, h]
    exact (Algebra.commutes _ _).symm
  have hτ : ∀ w : A, Commute w Y → Commute ((β : A) * (σ w).unop * ((β⁻¹ : Aˣ) : A)) Y := by
    intro w hw
    have hsh : Commute (σ w).unop (σ (Y : A)).unop := by
      show _ = _
      rw [← shmul, ← shmul, hw.eq]
    have hc : Commute ((β : A) * (σ w).unop * ((β⁻¹ : Aˣ) : A))
        ((β : A) * (σ (Y : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
      show _ = _
      simp only [mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc (σ w).unop, hsh.eq, mul_assoc]
    rw [hτY] at hc
    have h2 := (Algebra.commute_algebraMap_right ((s⁻¹ : Kˣ) : K) _).mul_right hc
    rw [← mul_assoc (algebraMap K A ((s⁻¹ : Kˣ) : K)), ← map_mul, Units.inv_mul, map_one,
      one_mul] at h2
    exact Commute.units_inv_right_iff.mp h2

  have e : a * (β : A) = ((k⁻¹ : Aˣ) : A) * ((k : A) * (a * β) * (σ (k : A)).unop) *
      (σ ((k⁻¹ : Aˣ) : A)).unop := by
    simp only [mul_assoc, shinv', shc, mul_one, Units.inv_mul_cancel_left]
  rw [hk, ← Algebra.commutes (lam : K), hkz, Units.val_mul, shmul] at e
  have ha : a = algebraMap K A lam * ((z : A) * ((m : A) * (σ (m : A)).unop) * (σ (z : A)).unop *
      ((β⁻¹ : Aˣ) : A)) := by
    calc a = a * β * ((β⁻¹ : Aˣ) : A) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [e]; simp only [mul_assoc]

  have hbi : (σ ((β⁻¹ : Aˣ) : A)).unop = ((β⁻¹ : Aˣ) : A) := by
    have h := shinv β
    rw [hβ] at h
    calc (σ ((β⁻¹ : Aˣ) : A)).unop = (σ ((β⁻¹ : Aˣ) : A)).unop * β * ((β⁻¹ : Aˣ) : A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h, one_mul]
  let mu : Aˣ := ⟨(σ (m : A)).unop, (σ ((m⁻¹ : Aˣ) : A)).unop, shinv' m, shinv m⟩
  let m' : Aˣ := m * mu * β⁻¹
  have hm' : (m' : A) = m * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) := rfl
  have hm'c : (m' : A) = ((z⁻¹ : Aˣ) : A) * (algebraMap K A ((lam⁻¹ : Kˣ) : K) * a) *
      ((β : A) * (σ ((z⁻¹ : Aˣ) : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
    rw [hm', ha, ← mul_assoc (algebraMap K A ((lam⁻¹ : Kˣ) : K)), ← map_mul, Units.inv_mul,
      map_one, one_mul]
    simp only [mul_assoc, Units.inv_mul_cancel_left, shc]
  have hmY : Commute (m' : A) Y := by
    rw [hm'c]
    exact ((hzY.units_inv_left).mul_left
      ((Algebra.commute_algebraMap_left _ _).mul_left haY)).mul_left (hτ _ hzY.units_inv_left)
  have hmτ : (β : A) * (σ (m' : A)).unop * ((β⁻¹ : Aˣ) : A) = m' := by
    rw [hm', shmul, shmul, hσ, hbi]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  obtain ⟨v, hvY, hv⟩ := H m' hm' hmY hmτ
  have h3 : (m : A) * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) =
      v * β * (σ (v : A)).unop * ((β⁻¹ : Aˣ) : A) := by
    rw [← hm', hv]; simp only [mul_assoc]
  have hmm := (Units.mul_left_inj β⁻¹).mp h3
  refine ⟨z * v, by rw [Units.val_mul]; exact hzY.mul_left hvY, ?_⟩
  rw [Units.val_mul, shmul, ha, hmm]
  simp only [mul_assoc]

end GlobalTheory
