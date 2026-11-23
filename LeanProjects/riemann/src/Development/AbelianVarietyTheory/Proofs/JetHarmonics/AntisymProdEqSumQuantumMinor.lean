import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.ScalarColsMinor

noncomputable def bord {p m : ℕ} (M : Matrix (Fin (p + m)) (Fin p) ℂ) (c : Fin m → Fin (p + m)) :
    Matrix (Fin (p + m)) (Fin (p + m)) ℂ :=
  Matrix.of fun a : Fin (p + m) => Fin.append (M a) (fun k : Fin m => if a = c k then (1 : ℂ) else 0)

theorem det_bord {p m : ℕ} (M : Matrix (Fin (p + m)) (Fin p) ℂ) (c : Fin m → Fin (p + m)) :
    (bord M c).det = ∑ σ : Equiv.Perm (Fin (p + m)),
      if (fun k => σ (Fin.natAdd p k)) = c then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, M (σ (Fin.castAdd m k)) k else 0 := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fin.prod_univ_add]
  simp only [bord, Matrix.of_apply, Fin.append_left, Fin.append_right]
  rw [Finset.prod_boole]
  by_cases h : (fun k => σ (Fin.natAdd p k)) = c
  · rw [if_pos h, if_pos (fun k _ => congrFun h k), mul_one]
  · rw [if_neg h, if_neg (fun hh => h (funext fun k => hh k (Finset.mem_univ _)))]
    simp

theorem sum_perm_eq {A : Type} [AddCommGroup A] [Module ℂ A] {p m : ℕ}
    (M : Matrix (Fin (p + m)) (Fin p) ℂ) (F : (Fin m → Fin (p + m)) → A) :
    ∑ σ : Equiv.Perm (Fin (p + m)),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, M (σ (Fin.castAdd m k)) k) •
        F (fun k => σ (Fin.natAdd p k)) = ∑ c, (bord M c).det • F c := by
  simp only [det_bord, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  simp

theorem det_bord_mul {p m : ℕ} (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (N : Matrix (Fin p) (Fin p) ℂ)
    (c : Fin m → Fin (p + m)) : (bord (Λ * N) c).det = N.det * (bord Λ c).det := by
  have h : bord (Λ * N) c = bord Λ c * (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks N 0 0 (1 : Matrix (Fin m) (Fin m) ℂ))) := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp [bord, Matrix.mul_apply]
    · simp [bord, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    mul_comm]

theorem det_bord_perm {p m : ℕ} (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (c : Fin m → Fin (p + m))
    (τ : Equiv.Perm (Fin m)) :
    (bord Λ (fun k => c (τ k))).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (bord Λ c).det := by
  have h : bord Λ (fun k => c (τ k)) = (bord Λ c).submatrix id
      (finSumFinEquiv.permCongr (Equiv.sumCongr (1 : Equiv.Perm (Fin p)) τ)) := by
    ext a b
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp [bord]
    · simp [bord]
  rw [h, Matrix.det_permute', Equiv.Perm.sign_permCongr]
  have := Equiv.Perm.sign_sumCongr (1 : Equiv.Perm (Fin p)) τ
  simp only [Equiv.Perm.sumCongr] at this
  rw [this]
  simp

theorem prod_ofFn_sum {A : Type} [Ring A] [Algebra ℂ A] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℂ)
    (T : Fin m → Fin n → A) :
    (List.ofFn fun k => ∑ d, Q k d • T k d).prod =
      ∑ d : Fin m → Fin n, (∏ k, Q k (d k)) • (List.ofFn fun k => T k (d k)).prod := by
  have h := (MultilinearMap.mkPiAlgebraFin ℂ m A).map_sum (fun k d => Q k d • T k d)
  simp only [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply] at h
  exact h

theorem sum_det_qminor {A : Type} [Ring A] [Algebra ℂ A] {p m : ℕ} (E : Fin (p + m) → Fin (p + m) → A)
    (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (d : Fin m → Fin (p + m)) (w : ℂ) :
    ∑ c : Fin m → Fin (p + m), (bord Λ c).det • qminor E c d w =
      ((m.factorial : ℕ) : ℂ) • ∑ c : Fin m → Fin (p + m), (bord Λ c).det •
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c k) (d k)).prod := by
  simp only [qminor, Finset.smul_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin m))))]
  rw [Finset.sum_comm]
  have h : ∀ τ : Equiv.Perm (Fin m), ∑ c : Fin m → Fin (p + m), (bord Λ c).det •
      (((Equiv.Perm.sign τ : ℤ) : A) *
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c (τ k)) (d k)).prod) =
      ∑ c : Fin m → Fin (p + m), (bord Λ c).det •
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c k) (d k)).prod := by
    intro τ
    refine Fintype.sum_equiv (Equiv.arrowCongr τ.symm (Equiv.refl _)) _ _ fun c => ?_
    have hc : (Equiv.arrowCongr τ.symm (Equiv.refl _)) c = fun k => c (τ k) := by
      ext k; simp
    rw [hc, det_bord_perm, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_comm]
  rw [Finset.sum_congr rfl fun τ _ => h τ, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul]

theorem antisym_prod_eq_sum_qminor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin m) (Fin (p + m)) ℂ) (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (N : Matrix (Fin p) (Fin p) ℂ) (w : ℂ), ∑ σ : Equiv.Perm (Fin (p + m)), (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, (Λ * N) (σ (Fin.castAdd m k)) k) • (List.ofFn fun k : Fin m => ∑ d, Q k d • Tm E (w - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod = N.det • ∑ c : Fin m → Fin (p + m), ∑ d : Fin m → Fin (p + m), ((Matrix.of fun a : Fin (p + m) => Fin.append (Λ a) (fun k : Fin m => if a = c k then (1 : ℂ) else 0)).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w := by
  intro A _ _ p m E Q Λ N w
  have h1 := sum_perm_eq (Λ * N) (fun c : Fin m → Fin (p + m) =>
    (List.ofFn fun k : Fin m => ∑ d, Q k d • Tm E (w - ((k : ℕ) : ℂ)) (c k) d).prod)
  rw [h1]
  change _ = N.det • ∑ c : Fin m → Fin (p + m), ∑ d : Fin m → Fin (p + m),
    ((bord Λ c).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w
  rw [Finset.sum_comm]
  have hf : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have h2 : ∀ d : Fin m → Fin (p + m), ∑ c : Fin m → Fin (p + m),
      ((bord Λ c).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w =
      ∑ c : Fin m → Fin (p + m), (bord Λ c).det • (∏ k, Q k (d k)) •
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c k) (d k)).prod := by
    intro d
    simp only [mul_comm (bord Λ _).det, mul_smul]
    rw [← Finset.smul_sum, ← Finset.smul_sum, sum_det_qminor, smul_smul _ ((m.factorial : ℕ) : ℂ),
      inv_mul_cancel₀ hf, one_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _
  rw [Finset.sum_congr rfl fun d _ => h2 d, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [det_bord_mul, mul_smul, prod_ofFn_sum Q (fun k d => Tm E (w - ((k : ℕ) : ℂ)) (c k) d),
    Finset.smul_sum (r := (bord Λ c).det)]

end GlobalTheory.ScalarColsMinor
