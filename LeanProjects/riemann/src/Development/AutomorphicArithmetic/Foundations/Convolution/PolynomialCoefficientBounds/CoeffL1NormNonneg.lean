import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.MatrixEntryAbsSumUnitaryLieCoordinatesSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenRed
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenFund
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenTrunc

open MvPolynomial Filter Topology

private noncomputable def coeffL1Norm {ι : Type} (p : MvPolynomial ι ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖p.coeff α‖

private theorem coeffL1Norm_nonneg {ι : Type} (p : MvPolynomial ι ℂ) : 0 ≤ coeffL1Norm p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem coeffL1Norm_mul {ι : Type} (p q : MvPolynomial ι ℂ) :
    coeffL1Norm (p * q) ≤ coeffL1Norm p * coeffL1Norm q := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).2.1

private theorem coeffL1Norm_C_mul {ι : Type} (c : ℂ) (p : MvPolynomial ι ℂ) :
    coeffL1Norm (C c * p) = ‖c‖ * coeffL1Norm p := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p p).2.2.1 c

private theorem coeffL1Norm_sum {ι κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι ℂ) :
    coeffL1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffL1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffL1Norm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h : coeffL1Norm (f a + ∑ i ∈ s, f i) ≤ coeffL1Norm (f a) + coeffL1Norm (∑ i ∈ s, f i) :=
      (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι _ _).1
    linarith

private theorem gen_inv {τ : Type} {n : ℕ} (w : τ → Equiv.Perm (Fin n))
    (g : MvPolynomial (τ × Fin n) ℂ) :
    rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2))
      (aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) g)
    = aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) g := by
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext ti
  conv_rhs => rw [← rename_esymm (Fin n) ℂ (ti.2 + 1) (w ti.1)]
  rw [rename_rename, rename_rename]
  rfl

theorem UpperTheory.ConvolutionTheory.FX.generators0 :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ), ∃ K : ℝ, ∀ (k : ℕ) (P : MvPolynomial (τ × Fin n) ℂ), P.totalDegree ≤ k → (∀ w : τ → Equiv.Perm (Fin n), rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) P = P) → ∃ G : MvPolynomial (τ × Fin n) ℂ, aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) G = P ∧ G.totalDegree ≤ k ∧ (∑ α ∈ (G).support, ‖(G).coeff α‖) ≤ K ^ (k + 1) * (∑ α ∈ (P).support, ‖(P).coeff α‖) := by
  intro τ _ _ n
  obtain ⟨K, hK, hred⟩ := UpperTheory.ConvolutionTheory.FX.gen_reduce τ n
  choose G hG hGb using hred
  choose F hF using fun β : τ × Fin n → Fin n => UpperTheory.ConvolutionTheory.FX.gen_fund τ n (fun u => (β u : ℕ))
  set M : ℝ := ∑ β, coeffL1Norm (F β) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => coeffL1Norm_nonneg _
  have hFM : ∀ β, coeffL1Norm (F β) ≤ M := fun β =>
    Finset.single_le_sum (f := fun β => coeffL1Norm (F β)) (fun _ _ => coeffL1Norm_nonneg _) (Finset.mem_univ β)
  clear_value M
  refine ⟨K + M, fun k P hP hinv => ?_⟩
  set N : ℕ := Fintype.card (τ → Equiv.Perm (Fin n)) with hN
  have hN1 : 1 ≤ N := Fintype.card_pos
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmon : ∀ α, aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1)))
      (∑ β, G α β * F β) = ∑ w : τ → Equiv.Perm (Fin n),
        rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) (monomial α (1 : ℂ)) := by
    intro α
    rw [hG α, map_sum]
    simp only [map_mul, hF, map_sum, gen_inv, Finset.mul_sum]
    exact Finset.sum_comm
  have hP' : P = ∑ α ∈ P.support, C (P.coeff α) * monomial α (1 : ℂ) := by
    conv_lhs => rw [P.as_sum]
    simp only [C_mul_monomial, mul_one]
  have hE : aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1)))
      (C (N : ℂ)⁻¹ * ∑ α ∈ P.support, C (P.coeff α) * ∑ β, G α β * F β) = P := by
    have h1 : ∑ w : τ → Equiv.Perm (Fin n),
        rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) P = C (N : ℂ) * P := by
      simp only [hinv, Finset.sum_const, Finset.card_univ, ← hN, nsmul_eq_mul, map_natCast]
    have h2 : ∑ α ∈ P.support, C (P.coeff α) * ∑ w : τ → Equiv.Perm (Fin n),
        rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) (monomial α (1 : ℂ)) = C (N : ℂ) * P := by
      rw [← h1]
      conv_rhs => rw [hP']
      simp only [map_sum, map_mul, rename_C, Finset.mul_sum]
      exact Finset.sum_comm
    rw [map_mul, map_sum]
    simp only [map_mul (aeval _) (C _), hmon, aeval_C, algebraMap_eq]
    rw [h2, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hNC, C_1, one_mul]
  obtain ⟨G', h1, h2, h3⟩ := UpperTheory.ConvolutionTheory.FX.gen_trunc τ n k _ (by rw [hE]; exact hP)
  refine ⟨G', h1.trans hE, h2, h3.trans ?_⟩
  change coeffL1Norm _ ≤ _
  have hb : ∀ α ∈ P.support, coeffL1Norm (∑ β, G α β * F β) ≤ (K + M) ^ (k + 1) := by
    intro α hα
    have hd : α.degree ≤ k := (le_totalDegree hα).trans hP
    calc _ ≤ ∑ β, coeffL1Norm (G α β * F β) := coeffL1Norm_sum _ _
      _ ≤ ∑ β, coeffL1Norm (G α β) * M := Finset.sum_le_sum fun β _ =>
          (coeffL1Norm_mul _ _).trans (mul_le_mul_of_nonneg_left (hFM β) (coeffL1Norm_nonneg _))
      _ = (∑ β, coeffL1Norm (G α β)) * M := by rw [Finset.sum_mul]
      _ ≤ K ^ α.degree * M := mul_le_mul_of_nonneg_right (hGb α) hM0
      _ ≤ K ^ k * M := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK hd) hM0
      _ ≤ (K + M) ^ k * (K + M) :=
          mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) k) (by linarith) hM0
            (pow_nonneg (by linarith) k)
      _ = _ := (pow_succ _ _).symm
  have hn : ‖(N : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hN1)
  rw [coeffL1Norm_C_mul]
  refine (mul_le_of_le_one_left (coeffL1Norm_nonneg _) hn).trans ((coeffL1Norm_sum _ _).trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  rw [coeffL1Norm_C_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb α hα) (norm_nonneg _)
