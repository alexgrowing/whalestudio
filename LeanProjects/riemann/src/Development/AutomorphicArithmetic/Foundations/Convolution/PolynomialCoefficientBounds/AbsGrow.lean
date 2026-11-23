import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Reduce
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Taylor

open PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.FX.abs_growth :
    ∀ (τ : Type) [Fintype τ] [Nonempty τ] (n : ℕ) (C : ℝ), ∃ K : ℝ, 1 ≤ K ∧ ∀ (κ A V : Type) (r : ℕ) [CommRing A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [Module A V]
    [IsScalarTower ℂ A V] (Z : τ × Fin n → A) (H : κ → A) (I : Fin r → A) (t : Multiplicative (Fin r → ℝ) →* A)
    (c : V →ₗ[ℂ] ((Fin r → ℝ) → ℂ)) (idx : Fin n → Fin r) (Λ : τ × Fin n → ℂ) (h : κ → EP (Fin r)) (good : Set κ),
    AbsSys Z H I t c idx Λ h good C → ∀ (φ : V) (R : ℝ), ∃ B : ℝ, ∀ (α : τ × Fin n →₀ ℕ) (x : Fin r → ℝ), ‖x‖ ≤ R →
    ‖c (MvPolynomial.aeval (fun q => algebraMap ℂ A (Λ q) + I (idx q.2)) (MvPolynomial.monomial α (1 : ℂ)) • φ) x‖ ≤ B * K ^ α.degree := by
  classical
  intro τ _ _ n C
  obtain ⟨K, hK, hR⟩ := UpperTheory.ConvolutionTheory.FX.reduce τ n
  have hC : (1 : ℝ) ≤ max |C| 1 := le_max_right _ _
  refine ⟨K * max |C| 1, one_le_mul_of_one_le_of_one_le hK hC, ?_⟩
  intro κ A V r _ _ _ _ _ _ Z H I t c idx Λ h good S φ R
  set ξ : τ × Fin n → A := fun q => algebraMap ℂ A (Λ q) + I (idx q.2) with hξ
  have cen : ∀ (G : MvPolynomial (τ × Fin n) ℂ) (ψ : V),
      c (MvPolynomial.aeval Z G • ψ) = c (MvPolynomial.aeval ξ (MvPolynomial.aeval blockE G) • ψ) := fun G => by
    induction G using MvPolynomial.induction_on with
    | C a => intro ψ; simp
    | add p q hp hq => intro ψ; simp only [map_add, add_smul, hp, hq]
    | mul_X p j hp =>
      intro ψ
      rw [map_mul, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, mul_smul, hp, smul_comm, S.cen, mul_comm, mul_smul]
  have L : ∀ P : MvPolynomial (Fin r) ℂ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (α : τ × Fin n →₀ ℕ) (x : Fin r → ℝ), ‖x‖ ≤ R →
      ‖c ((α.prod (fun p e => Z p ^ e) * MvPolynomial.aeval I P) • φ) x‖ ≤ B * max |C| 1 ^ α.degree := fun P => by
    induction P using MvPolynomial.induction_on' with
    | monomial β a =>
      obtain ⟨B, hB⟩ := S.bound φ β R
      refine ⟨‖a‖ * |B|, by positivity, fun α x hx => ?_⟩
      rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def, mul_smul_comm, smul_assoc, map_smul, Pi.smul_apply, norm_smul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ((hB α x hx).trans ((le_abs_self _).trans ?_)) (norm_nonneg _)
      rw [abs_mul, abs_pow]
      gcongr
      exact le_max_left _ _
    | add p q hp hq =>
      obtain ⟨B, hB, h1⟩ := hp
      obtain ⟨B', hB', h2⟩ := hq
      refine ⟨B + B', by positivity, fun α x hx => ?_⟩
      rw [map_add, mul_add, add_smul, map_add, Pi.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (h1 α x hx) (h2 α x hx))
  choose B hB0 hB using fun β : τ × Fin n → Fin n => L (∏ u, (MvPolynomial.C (Λ u) + MvPolynomial.X (idx u.2)) ^ (β u : ℕ))
  refine ⟨∑ β, B β, fun α x hx => ?_⟩
  obtain ⟨G, h1, h2, h3⟩ := hR α
  have hl : ∀ p : MvPolynomial (τ × Fin n) ℂ, 0 ≤ l1 p := fun p => Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [h1, map_sum, Finset.sum_smul, map_sum, Finset.sum_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  have e : MvPolynomial.aeval ξ (∏ u, (MvPolynomial.X u : MvPolynomial (τ × Fin n) ℂ) ^ (β u : ℕ)) =
      MvPolynomial.aeval I (∏ u, (MvPolynomial.C (Λ u) + MvPolynomial.X (idx u.2) : MvPolynomial (Fin r) ℂ) ^ (β u : ℕ)) := by
    simp [hξ]
  rw [map_mul, mul_smul, ← cen, e, ← mul_smul, MvPolynomial.aeval_def Z, MvPolynomial.eval₂_eq, Finset.sum_mul, Finset.sum_smul,
    map_sum, Finset.sum_apply]
  have hG : l1 (G β) ≤ K ^ α.degree := (Finset.single_le_sum (fun β _ => hl (G β)) (Finset.mem_univ β)).trans h2
  calc _ ≤ ∑ γ ∈ (G β).support, ‖(G β).coeff γ‖ * (B β * max |C| 1 ^ α.degree) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun γ hγ => ?_)
        rw [mul_assoc, ← Algebra.smul_def, smul_assoc, map_smul, Pi.smul_apply, norm_smul]
        refine mul_le_mul_of_nonneg_left ((hB β γ x hx).trans ?_) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC ((MvPolynomial.le_totalDegree hγ).trans (h3 β))) (hB0 β)
    _ = l1 (G β) * (B β * max |C| 1 ^ α.degree) := by rw [← Finset.sum_mul]; rfl
    _ ≤ K ^ α.degree * (B β * max |C| 1 ^ α.degree) := mul_le_mul_of_nonneg_right hG (mul_nonneg (hB0 β) (by positivity))
    _ = _ := by rw [mul_pow]; ring
