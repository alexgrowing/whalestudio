import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem mul_single_mul_apply (M N : Matrix (Fin r) (Fin r) ℤ) (i₀ i j : Fin r) :
    (M * Matrix.single i₀ i₀ (1:ℤ) * N) i j = M i i₀ * N i₀ j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single i₀]
  · congr 1
    simp [Matrix.mul_apply, Matrix.single_apply]
  · intro b _ hb
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hb]
  · simp

theorem mul_single_apply' (M : Matrix (Fin r) (Fin r) ℤ) (i₀ i j : Fin r) :
    (M * Matrix.single i₀ i₀ (1:ℤ)) i j = if j = i₀ then M i i₀ else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
  · by_cases h : j = i₀
    · subst h; simp
    · simp [Matrix.single_apply, Ne.symm h, h]
  · intro b _ hb
    simp [Matrix.single_apply, Ne.symm hb]
  · simp

theorem Tens.xe_xi (T : Tens D D' W) (i₀ : Fin r) (y : D.X) :
    T.xe (T.xi i₀ y) = Pi.single i₀ y := by
  simp [Tens.xi]

theorem Tens.xe_smul_xi (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (i₀ : Fin r) (y : D.X) (i : Fin r) :
    letI := T.mod s
    T.xe (a • T.xi i₀ y) i = TensO.mat s a i i₀ • y := by
  letI := T.mod s
  rw [Tens.xe_smul]
  simp only [Tens.xe_xi]
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem TensO.mat_star_idem_mul_binv {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    TensO.mat s (star (TensO.idem s i₀) * TensO.binv s) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 := by
  rw [TensO.mat_mul, TensO.star_def]
  show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (Matrix.single i₀ i₀ (1:ℤ)).transpose *
      (s.1 : Matrix (Fin r) (Fin r) ℤ) * ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = _
  rw [Matrix.transpose_single, Matrix.mul_assoc _ (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.mul_one]

theorem TensO.mat_star_idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    TensO.mat s (star (TensO.idem s i₀)) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) := by
  rw [TensO.star_def]
  show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (Matrix.single i₀ i₀ (1:ℤ)).transpose *
      (s.1 : Matrix (Fin r) (Fin r) ℤ) = _
  rw [Matrix.transpose_single]

theorem SymUnit.inv_col_ne {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    ∃ i, ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) i i₀ ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 := congrFun (congrFun (Units.mul_inv s.1) i₀) i₀
  rw [Matrix.mul_apply, Finset.sum_eq_zero (fun k _ => by rw [h k, mul_zero]), Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

theorem tens_factor_latt : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (s : SymUnit r) (i₀ : Fin r), letI := T.mod s;
    (∀ y, T.xp i₀ (T.xi i₀ y) = y) ∧ (∀ z, T.xi i₀ (T.xp i₀ z) = TensO.idem s i₀ • z) ∧
    Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) ∧
    ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y := by
  intro R _ _ D D' r W T s i₀
  letI := T.mod s
  have key : ∀ y i, T.xe (star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) i =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) i i₀ • y := by
    intro y i
    rw [← mul_smul, Tens.xe_smul_xi, TensO.mat_star_idem_mul_binv, mul_single_apply']
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    show T.xe (T.xi i₀ y) i₀ = y
    rw [Tens.xe_xi]; simp
  · intro z
    apply T.xe.injective
    funext i
    rw [Tens.xe_xi, Tens.xe_smul]
    show Pi.single (M := fun _ => D.X) i₀ (T.xe z i₀) i = _
    simp only [TensO.idem, TensO.ofMat, TensO.mat, Matrix.single_apply]
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  · intro y y' h
    obtain ⟨i, hi⟩ := SymUnit.inv_col_ne s i₀
    have h' := congrArg (fun z => T.xe z i) h
    simp only [key] at h'
    exact smul_right_injective D.X hi h'
  · intro z
    refine ⟨∑ j, (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ j • T.xe z j, ?_⟩
    apply T.xe.injective
    funext i
    rw [key, Tens.xe_smul, TensO.mat_star_idem, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_single_mul_apply, mul_smul]
end GlobalTheory.Mum
