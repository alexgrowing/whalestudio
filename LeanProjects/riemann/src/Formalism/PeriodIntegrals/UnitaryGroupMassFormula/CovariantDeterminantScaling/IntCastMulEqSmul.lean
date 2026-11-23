import Formalism.PeriodIntegrals.ContractionsCovariantIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

open Matrix Finset

noncomputable section

namespace PI.QnCovDetW

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem sum_fun_eq_sum_perm {M : Type*} [AddCommMonoid M] {n : ℕ}
    (g : (Fin n → Fin n) → M) (hg : ∀ c, ¬ Function.Injective c → g c = 0) :
    ∑ c, g c = ∑ σ : Equiv.Perm (Fin n), g σ := by
  classical
  have h2 : ∑ σ : Equiv.Perm (Fin n), g σ = ∑ c ∈ Finset.univ.filter Function.Injective, g c := by
    refine Finset.sum_nbij (fun σ => (σ : Fin n → Fin n)) (fun σ _ => by simpa using σ.injective)
      (by intro a _ b _ h; exact DFunLike.coe_injective h) (by
        intro c hc
        have hc' : Function.Injective c := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
        exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.1 hc'),
          Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩) (fun _ _ => rfl)
  rw [h2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rfl
  · exact hg c h

theorem intCast_mul_eq_smul {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (x : A) :
    (z : A) * x = (z : ℂ) • x := by
  rw [Algebra.smul_def, map_intCast]

private theorem qminor_rowperm_lemma {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) (π : Equiv.Perm (Fin t)) :
    qminor E (a ∘ π) b u = ((Equiv.Perm.sign π : ℤ) : A) * qminor E a b u := by
  unfold qminor
  rw [Finset.mul_sum]
  have hs : ((Equiv.Perm.sign π : ℤ) : A) * ((Equiv.Perm.sign π : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  refine Fintype.sum_equiv (Equiv.mulLeft π) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, Function.comp_apply]
  rw [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, ← mul_assoc, hs, one_mul]

private theorem qminor_colperm_lemma_2 {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (a : Fin (m + 1) → Fin n) (u : ℂ) (τ : Equiv.Perm (Fin (m + 1))) :
    ∀ b : Fin (m + 1) → Fin n, qminor E a (b ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u := by
  have hcl : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top τ
  induction hcl using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro b
    rw [quantumMinor_adjacent_col_swap E hE a b i u, Equiv.Perm.sign_swap (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne]
    simp
  | one =>
    intro b
    simp
  | mul x y _ _ hx hy =>
    intro b
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy, hx, Equiv.Perm.sign_mul,
      mul_comm (Equiv.Perm.sign x), Units.val_mul, Int.cast_mul, mul_assoc]

theorem qminor_perm_perm {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (σ τ : Equiv.Perm (Fin n)) (u : ℂ) :
    qminor E σ τ u =
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) • qdet E u := by
  rcases n with _ | m
  · have hσ : σ = 1 := Equiv.ext fun i => i.elim0
    have hτ : τ = 1 := Equiv.ext fun i => i.elim0
    subst hσ hτ
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, mul_one, one_smul, Equiv.Perm.coe_one]
    rfl
  · have h1 := qminor_rowperm_lemma E id (⇑τ) u σ
    have h2 := qminor_colperm_lemma_2 E hE id u τ id
    simp only [Function.id_comp] at h1 h2
    rw [h1, h2, intCast_mul_eq_smul, intCast_mul_eq_smul, smul_smul]
    rfl

theorem sum_sign_prod_left {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (σ k) k = P.det := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]

theorem sum_sign_prod_right {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) :
    ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, Q k (τ k) = Q.det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul, Matrix.transpose_apply]

theorem qnCovDet_of_lin (h : PI.QnCovLin) : PI.QnCovDet := by
  intro A _ _ n E P Q hE hQP hPQ u
  have hrep : ∀ c : Fin n → Fin n, ¬ Function.Injective c → ∃ p q, p ≠ q ∧ c p = c q := by
    intro c hc
    by_contra hne
    push_neg at hne
    exact hc (fun p q hpq => by_contra fun h => hne p q h hpq)
  have hrow : ∀ c d : Fin n → Fin n, ¬ Function.Injective c → qminor E c d u = 0 := by
    intro c d hc
    obtain ⟨p, q, hpq, hcq⟩ := hrep c hc
    exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hpq hcq
  have hcol : ∀ c d : Fin n → Fin n, ¬ Function.Injective d → qminor E c d u = 0 := by
    intro c d hd
    obtain ⟨p, q, hpq, hdq⟩ := hrep d hd
    exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d u p q hpq hdq
  have key : qdet (Econj E P Q) u = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      ((((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (σ k) k) * (((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, Q k (τ k))) • qdet E u := by
    rw [show qdet (Econj E P Q) u = qminor (Econj E P Q) id id u from rfl, h A n n E P Q hQP id id u,
      sum_fun_eq_sum_perm]
    · refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [sum_fun_eq_sum_perm]
      · refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [qminor_perm_perm E hE σ τ u, smul_smul]
        congr 1
        try simp only [id_eq]
        ring
      · intro d hd
        rw [hcol _ d hd, smul_zero]
    · intro c hc
      exact Finset.sum_eq_zero (fun d _ => by rw [hrow c d hc, smul_zero])
  rw [key]
  simp_rw [← Finset.sum_smul]
  rw [← Finset.sum_mul_sum, sum_sign_prod_left, sum_sign_prod_right, ← Matrix.det_mul, hPQ,
    Matrix.det_one, one_smul]

end PI.QnCovDetW
