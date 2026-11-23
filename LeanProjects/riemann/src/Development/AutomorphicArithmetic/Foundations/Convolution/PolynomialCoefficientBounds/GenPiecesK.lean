import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenPieces

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.gen_piecesK :
    ∀ (τ κ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ) (F : KF (τ × Fin n) κ), (∀ w : τ → Equiv.Perm (Fin n), map (ren (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2))) F = F) → ∃ (K : ℝ) (G : ℕ → MvPolynomial κ (MvPolynomial (τ × Fin n) ℂ)), ∀ k, map (aeval (blockE (τ := τ) (n := n)) : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ).toRingHom (G k) = pieceK k F ∧ (G k).support ⊆ F.support ∧ ∀ β, ((G k).coeff β).totalDegree ≤ k ∧ l1 ((G k).coeff β) ≤ K ^ (k + 1) / k.factorial := by
  intro τ κ _ _ n F hF
  classical
  have h : ∀ β : κ →₀ ℕ, ∃ (K : ℝ) (G : ℕ → MvPolynomial (τ × Fin n) ℂ), ∀ k,
      aeval blockE (G k) = piece k (F.coeff β) ∧ (G k).totalDegree ≤ k ∧
        l1 (G k) ≤ K ^ (k + 1) / k.factorial := fun β =>
    UpperTheory.ConvolutionTheory.FX.gen_pieces τ n (F.coeff β) (fun w => by
      have := congrArg (fun P => MvPolynomial.coeff β P) (hF w)
      simpa only [coeff_map] using this)
  choose K G hG using h
  have hc : ∀ k β, (∑ γ ∈ F.support, monomial γ (G γ k) :
      MvPolynomial κ (MvPolynomial (τ × Fin n) ℂ)).coeff β = if β ∈ F.support then G β k else 0 := by
    intro k β
    simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  have hK0 : 0 ≤ ∑ γ ∈ F.support, |K γ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ γ ∈ F.support, |K γ|, fun k => ∑ γ ∈ F.support, monomial γ (G γ k), fun k => ⟨?_, ?_, fun β => ?_⟩⟩
  · rw [map_sum, pieceK]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [map_monomial, ← (hG γ k).1]
    rfl
  · intro β hβ
    rw [mem_support_iff, hc] at hβ
    by_contra hn
    exact hβ (if_neg hn)
  · rw [hc]
    split_ifs with hβ
    · refine ⟨(hG β k).2.1, (hG β k).2.2.trans ?_⟩
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc K β ^ (k + 1) ≤ |K β| ^ (k + 1) := by rw [← abs_pow]; exact le_abs_self _
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _)
            (Finset.single_le_sum (f := fun γ => |K γ|) (fun _ _ => abs_nonneg _) hβ) _
    · refine ⟨by simp, ?_⟩
      have : l1 (0 : MvPolynomial (τ × Fin n) ℂ) = 0 := by simp [l1]
      rw [this]
      positivity
