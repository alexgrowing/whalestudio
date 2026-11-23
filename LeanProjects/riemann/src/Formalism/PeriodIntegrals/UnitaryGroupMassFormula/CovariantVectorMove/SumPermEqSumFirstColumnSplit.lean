import Formalism.PeriodIntegrals.QmDefs
import Formalism.PeriodIntegrals.QmMove
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmMove

theorem prod_diff {A : Type*} [Ring A] {t : ℕ} (f g : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k) :
    (List.ofFn f).prod - (List.ofFn g).prod =
      ((List.ofFn f).take i).prod *
        (f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩ - g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩) *
        ((List.ofFn f).drop (i + 2)).prod := by
  rw [prod_ofFn_split_pair f i hi, prod_ofFn_split_pair g i hi, take_ofFn_congr g f i (fun k hk => h k (by omega) (by omega)),
    drop_ofFn_congr g f (i + 2) (fun k hk => h k (by omega) (by omega))]
  noncomm_ring

theorem sgn_mul_swap {A : Type*} [Ring A] {t : ℕ} (s : Equiv.Perm (Fin t))
    (hs : Equiv.Perm.sign s = -1) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign (τ * s) : ℤ) : A) = -((Equiv.Perm.sign τ : ℤ) : A) := by
  rw [Equiv.Perm.sign_mul, hs]
  push_cast
  simp

theorem step {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (s : Equiv.Perm (Fin t))
    (hs : Equiv.Perm.sign s = -1) (P Q X : Equiv.Perm (Fin t) → A)
    (hX : ∀ τ, X (τ * s) = X τ) (hPQ : ∀ τ, P (τ * s) - Q τ = X τ) :
    ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * Q τ = -∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * P τ := by
  have hz : ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * X τ = 0 := by
    have h1 : ∑ τ, ((Equiv.Perm.sign (τ * s) : ℤ) : A) * X (τ * s) =
        ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * X τ :=
      Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun τ => rfl)
    simp only [hX, sgn_mul_swap s hs, neg_mul, Finset.sum_neg_distrib] at h1
    exact eq_zero_of_eq_neg_self_of_algebra_complex _ h1.symm
  have h2 : ∑ τ, ((Equiv.Perm.sign (τ * s) : ℤ) : A) * P (τ * s) =
      ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * P τ :=
    Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun τ => rfl)
  have hP : ∀ τ, P (τ * s) = Q τ + X τ := fun τ => by rw [← hPQ τ]; abel
  simp only [hP, sgn_mul_swap s hs, neg_mul, mul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, hz] at h2
  rw [← h2]
  simp only [neg_zero, add_zero, neg_neg]

theorem chain {A : Type*} [Ring A] (S : ℕ → A) : ∀ m : ℕ, (∀ p < m, S (p + 1) = -S p) →
    S m = (((-1 : ℤ) ^ m : ℤ) : A) * S 0
  | 0, _ => by simp
  | m + 1, h => by
    rw [h m (by omega), chain S m (fun p hp => h p (by omega))]
    push_cast
    rw [pow_succ]
    simp [mul_neg, neg_mul]

def phi0 (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (Fin.cycleRange p.1).symm * Equiv.Perm.decomposeFin.symm (0, p.2)

theorem firstColumnSplit_zero (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) : phi0 m (j, ρ) 0 = j := by
  simp [phi0, Equiv.Perm.mul_apply]

theorem firstColumnSplit_succ (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) (k : Fin m) :
    phi0 m (j, ρ) k.succ = j.succAbove (ρ k) := by
  simp [phi0, Equiv.Perm.mul_apply]

theorem sign_firstColumnSplit (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (phi0 m (j, ρ)) = (-1) ^ (j : ℕ) * Equiv.Perm.sign ρ := by
  simp [phi0, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign]

theorem firstColumnSplit_bijective (m : ℕ) : Function.Bijective (phi0 m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    have hj : j = j' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ 0) h
      simpa [firstColumnSplit_zero] using this
    subst hj
    have : τ = τ' := by
      refine Equiv.ext fun k => ?_
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.succ) h
      simp only [firstColumnSplit_succ] at this
      exact Fin.succAbove_right_inj.mp this
    rw [this]
  · simp [Fintype.card_prod, Fintype.card_perm, Nat.factorial_succ]

theorem sum_perm_eq_sum_firstColumnSplit {M : Type*} [AddCommMonoid M] (m : ℕ) (g : Equiv.Perm (Fin (m + 1)) → M) :
    ∑ τ, g τ = ∑ j : Fin (m + 1), ∑ ρ : Equiv.Perm (Fin m), g (phi0 m (j, ρ)) := by
  rw [(Fintype.sum_bijective (phi0 m) (firstColumnSplit_bijective m) (fun p => g (phi0 m p)) g (fun _ => rfl)).symm,
    Fintype.sum_prod_type]

theorem sum_phiL {M : Type*} [AddCommMonoid M] (m : ℕ) (g : Equiv.Perm (Fin (m + 1)) → M) :
    ∑ τ, g τ = ∑ j : Fin (m + 1), ∑ ρ : Equiv.Perm (Fin m), g (lastColumnSplit m (j, ρ)) := by
  rw [(Fintype.sum_bijective (lastColumnSplit m) (lastColumnSplit_bijective m) (fun p => g (lastColumnSplit m p)) g
    (fun _ => rfl)).symm, Fintype.sum_prod_type]

theorem phiL_castSucc (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) (k : Fin m) :
    lastColumnSplit m (j, ρ) k.castSucc = j.succAbove (ρ k) := by
  simp [lastColumnSplit, Equiv.Perm.mul_apply, extendLast_castSucc, cycleToLast_castSucc]

theorem phiL_last (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    lastColumnSplit m (j, ρ) (Fin.last m) = j := by
  simp [lastColumnSplit, Equiv.Perm.mul_apply, extendLast_last, cycleToLast_last]

theorem phiL_sign (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (lastColumnSplit m (j, ρ)) = (-1) ^ (m - (j : ℕ)) * Equiv.Perm.sign ρ := by
  simp [lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast]

theorem fact_cancel {A : Type*} [Ring A] [Algebra ℂ A] (m : ℕ) (X Y : A)
    (h : (m.factorial : A) * X = (m.factorial : A) * Y) : X = Y := by
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have e : ∀ Z : A, Z = algebraMap ℂ A ((m.factorial : ℂ)⁻¹) * ((m.factorial : A) * Z) := by
    intro Z
    rw [← mul_assoc, ← map_natCast (algebraMap ℂ A), ← map_mul, inv_mul_cancel₀ hm, map_one, one_mul]
  rw [e X, e Y, h]

theorem neg_one_pow_sub (m j : ℕ) (hj : j ≤ m) :
    ((-1 : ℤ) ^ (m - j) : ℤ) = (-1) ^ m * (-1) ^ j := by
  rw [← pow_add]
  rw [show m + j = (m - j) + 2 * j by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

theorem icomm {A : Type*} [Ring A] (z : ℤ) (x : A) : (z : A) * x = x * (z : A) :=
  (Int.cast_commute z x).eq

end PI.UnitaryGroupMassFormula.QmMove
