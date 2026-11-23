import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCompletionFirstColumnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuantumDetCentralCoeffsConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleOfCharPolyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
open Matrix GlobalTheory.TorFin

namespace GlobalTheory

theorem capelli_tm_sub_eq {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (w x : ℂ)
    (a b : Fin n) :
    Formalism.REAL.Tm E (w - x) a b = w • (if a = b then (1 : A) else 0) + Formalism.REAL.Tm E (-x) a b := by
  unfold Formalism.REAL.Tm
  split_ifs <;> simp [Algebra.smul_def, sub_eq_add_neg, map_add, add_assoc]

theorem mul_single_mul_eq_vecMulVec {n : ℕ} (P P' : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P * Matrix.single a b 1 * P' = vecMulVec (fun i => P i a) (fun j => P' b j) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, vecMulVec_apply, Finset.sum_ite_eq, ite_and]

theorem rho_vecMulVec_isIntMod_invAlg : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A]
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ v φ : Fin n → ℂ, φ ⬝ᵥ v = 1 →
    IsIntMod (invAlg ρ) (leftIdl ρ {Y | ∃ u, φ ⬝ᵥ u = 0 ∧ Y = vecMulVec u φ}) (ρ (vecMulVec v φ)) := by
  intro n A _ _ ρ hρ v φ hφv
  cases n with
  | zero => simp [dotProduct] at hφv
  | succ m =>
  obtain ⟨P, P', hPP', hPv, hP'φ⟩ := GlobalTheory.T.matrix_completion_first_column m v φ hφv
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  obtain ⟨c, hcN, hcZ, hc⟩ := GlobalTheory.T.quantum_det_central_coeffs_conj (m+1) A ρ hρ P P' hPP'
  have hadj : ∀ X, ρ X ∈ Algebra.adjoin ℂ (Set.range ρ) := fun X => Algebra.subset_adjoin ⟨X, rfl⟩
  have hTm : ∀ w a b, Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P')) w a b
      ∈ Algebra.adjoin ℂ (Set.range ρ) := by
    intro w a b
    refine add_mem ?_ (hadj _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact zero_mem _
  have hE0 : ∀ a, ρ (P * Matrix.single a 0 1 * P') = ρ (vecMulVec (fun i => P i a) φ) := by
    intro a
    rw [mul_single_mul_eq_vecMulVec]
    congr 2
    funext j
    exact hP'φ j
  have hEH : ρ (P * Matrix.single 0 0 1 * P') = ρ (vecMulVec v φ) := by
    rw [hE0]
    congr 2
    funext i
    exact hPv i
  have hcol : ∀ a : Fin (m+1), a ≠ 0 → φ ⬝ᵥ (fun i => P i a) = 0 := by
    intro a ha
    have := congrFun (congrFun hP'P 0) a
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Ne.symm ha)] at this
    simpa [dotProduct, hP'φ] using this
  have hHI : ∀ x ∈ leftIdl ρ {Y | ∃ u, φ ⬝ᵥ u = 0 ∧ Y = vecMulVec u φ},
      ρ (vecMulVec v φ) * x ∈ leftIdl ρ {Y | ∃ u, φ ⬝ᵥ u = 0 ∧ Y = vecMulVec u φ} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, ⟨u, hu, rfl⟩, w, hw, rfl⟩ := hx
      have h1 : ρ (vecMulVec v φ) * ρ (vecMulVec u φ)
          = ρ (vecMulVec u φ) * ρ (vecMulVec v φ) - ρ (vecMulVec u φ) := by
        have := hρ (vecMulVec v φ) (vecMulVec u φ)
        rw [vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, hu, hφv, zero_smul, one_smul] at this
        have h0 : vecMulVec v (0 : Fin (m+1) → ℂ) = 0 := by ext i j; simp [vecMulVec_apply]
        rw [h0, zero_sub, map_neg] at this
        rw [eq_sub_iff_add_eq, ← sub_neg_eq_add, this]
        abel
      rw [← mul_assoc, h1, sub_mul, mul_assoc]
      exact sub_mem (Submodule.subset_span ⟨_, ⟨u, hu, rfl⟩, _, mul_mem (hadj _) hw, rfl⟩)
        (Submodule.subset_span ⟨_, ⟨u, hu, rfl⟩, w, hw, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  have hR : ∀ σ : Equiv.Perm (Fin (m+1)), ∃ d : ℕ → A, ∀ u : ℂ,
      (List.ofFn fun k : Fin m => Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P'))
        (u - ((k.succ : Fin (m+1)) : ℂ)) (σ k.succ) k.succ).prod
        = ∑ i ∈ Finset.range (m+1), u ^ i • d i := by
    intro σ
    obtain ⟨d, -, hd⟩ := GlobalTheory.prod_affine_polyMap_top m
      (fun k => if σ k.succ = k.succ then (1 : A) else 0)
      (fun k => Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P'))
        (-((k.succ : Fin (m+1)) : ℂ)) (σ k.succ) k.succ)
    exact ⟨d, fun u => by rw [← hd u]; congr 2; funext k; exact capelli_tm_sub_eq _ u _ _ _⟩
  choose d hd using hR
  refine GlobalTheory.T.integral_module_of_char_poly A (invAlg ρ) _ _ hHI (m+1) c
    (fun i => ∑ σ : Equiv.Perm (Fin (m+1)),
      if σ 0 = 0 then ((Equiv.Perm.sign σ : ℤ) : A) * d σ i else 0) hcN hcZ ?_
  intro u
  rw [← hc u]
  have hQ : ∑ k ∈ Finset.range (m+1), u ^ k • (∑ σ : Equiv.Perm (Fin (m+1)),
      if σ 0 = 0 then ((Equiv.Perm.sign σ : ℤ) : A) * d σ k else 0)
      = ∑ σ : Equiv.Perm (Fin (m+1)), if σ 0 = 0 then ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun k : Fin m => Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P'))
        (u - ((k.succ : Fin (m+1)) : ℂ)) (σ k.succ) k.succ).prod else 0 := by
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs
    · rw [hd σ u, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm]
    · simp
  rw [hQ]
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [List.ofFn_succ, List.prod_cons]
  simp only [id]
  by_cases h0 : σ 0 = 0
  · rw [if_pos h0]
    have hT : Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P')) (u - ((0 : Fin (m+1)) : ℂ)) (σ 0) 0
        = u • (1 : A) + ρ (vecMulVec v φ) := by
      unfold Formalism.REAL.Tm
      beta_reduce
      rw [if_pos h0, h0, hEH]
      simp [Algebra.smul_def]
    rw [hT, ← mul_assoc, ← mul_assoc, ← (Int.cast_commute _ _).eq, sub_self]
    exact zero_mem _
  · rw [if_neg h0, mul_zero, sub_zero]
    have hT : Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P')) (u - ((0 : Fin (m+1)) : ℂ)) (σ 0) 0
        = ρ (vecMulVec (fun i => P i (σ 0)) φ) := by
      unfold Formalism.REAL.Tm
      beta_reduce
      rw [if_neg h0, zero_add, hE0]
    rw [hT, ← zsmul_eq_mul]
    refine zsmul_mem ?_ _
    refine Submodule.subset_span ?_
    refine ⟨_, ⟨_, hcol _ h0, rfl⟩, _, Subalgebra.list_prod_mem _ ?_, rfl⟩
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact hTm _ _ _

end GlobalTheory
