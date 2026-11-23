import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem period_growth_mono_bound (x C : ℝ) (k K : ℕ) (hx : 0 ≤ x) (hk : k ≤ K) :
    C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ K := by
  have h1 : (1:ℝ) ≤ 1 + x := by linarith
  calc C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + x) ^ K :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hk) (le_max_right _ _)

theorem period_matrix_polynomial_growth : ∀ (n a d : ℕ) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (c : Fin d → Fin d → ℂ), DifferentiableOn ℂ τ (logDom n a) → (∀ s ∈ logDom n a, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) → (∀ s ∈ logDom n a, ∀ i j, τ s i j - τ s j i = c i j) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a d τ c hτ hpos hc

  have key : ∀ v : Fin d → ℝ, v ≠ 0 → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) →
      ‖∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro v hv
    apply GlobalTheory.upper_half_growth n a
    · have hij : ∀ i j, DifferentiableOn ℂ (fun s => τ s i j) (logDom n a) :=
        fun i j => differentiableOn_pi.1 (differentiableOn_pi.1 hτ i) j
      fun_prop
    · intro s hs; exact hpos s hs v hv
  have e1 : ∀ (M : Fin d → Fin d → ℂ) (i : Fin d),
      ∑ i', ∑ j', (((Pi.single i (1:ℝ) : Fin d → ℝ) i' : ℝ) : ℂ) * M i' j' * (((Pi.single i (1:ℝ) : Fin d → ℝ) j' : ℝ) : ℂ) = M i i := by
    intro M i
    simp [Pi.single_apply, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
  have e2 : ∀ (M : Fin d → Fin d → ℂ) (i j : Fin d),
      ∑ i', ∑ j', ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) i' : ℝ) : ℂ) * M i' j' * ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) j' : ℝ) : ℂ) = M i i + M j j + M i j + M j i := by
    intro M i j
    simp [Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
    ring
  have ne1 : ∀ i : Fin d, (Pi.single i (1:ℝ) : Fin d → ℝ) ≠ 0 := by
    intro i h
    have := congrFun h i
    simp at this
  have ne2 : ∀ i j : Fin d, (Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ) ≠ 0 := by
    intro i j h
    have := congrFun h i
    simp [Pi.single_apply] at this
    split_ifs at this <;> linarith

  have entry : ∀ i j : Fin d, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s i j‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro i j
    obtain ⟨C1, k1, h1⟩ := key _ (ne2 i j)
    obtain ⟨C2, k2, h2⟩ := key _ (ne1 i)
    obtain ⟨C3, k3, h3⟩ := key _ (ne1 j)
    refine ⟨(max C1 0 + max C2 0 + max C3 0 + ‖c i j‖) / 2, max k1 (max k2 k3), by positivity, ?_⟩
    intro s hs hl him
    set K := max k1 (max k2 k3)
    have hx : 0 ≤ ‖s‖ := norm_nonneg _
    have b1 := (h1 s hs hl him).trans (period_growth_mono_bound ‖s‖ C1 k1 K hx (by omega))
    have b2 := (h2 s hs hl him).trans (period_growth_mono_bound ‖s‖ C2 k2 K hx (by omega))
    have b3 := (h3 s hs hl him).trans (period_growth_mono_bound ‖s‖ C3 k3 K hx (by omega))
    rw [e2] at b1
    rw [e1] at b2 b3
    have hP : 1 ≤ (1 + ‖s‖) ^ K := one_le_pow₀ (by linarith)
    have hcc : ‖c i j‖ ≤ ‖c i j‖ * (1 + ‖s‖) ^ K := le_mul_of_one_le_right (norm_nonneg _) hP
    have hid : (2:ℂ) * τ s i j = (τ s i i + τ s j j + τ s i j + τ s j i) - τ s i i - τ s j j + c i j := by
      rw [← hc s hs i j]; ring
    have h2n : ‖(2:ℂ) * τ s i j‖ ≤ ‖τ s i i + τ s j j + τ s i j + τ s j i‖ + ‖τ s i i‖ + ‖τ s j j‖ + ‖c i j‖ := by
      rw [hid]
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_sub_le _ _).trans ?_
      gcongr
      exact norm_sub_le _ _
    rw [norm_mul] at h2n
    norm_num at h2n
    nlinarith
  choose Ce ke hCe hke using entry
  refine ⟨∑ i, ∑ j, Ce i j, Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2), ?_⟩
  intro s hs hl him
  set K := Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2)
  have hx : 0 ≤ ‖s‖ := norm_nonneg _
  have hP : 0 ≤ (1 + ‖s‖) ^ K := by positivity
  have hS : 0 ≤ ∑ i, ∑ j, Ce i j := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hCe i j
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hk : ke i j ≤ K := Finset.le_sup (f := fun p : Fin d × Fin d => ke p.1 p.2) (Finset.mem_univ (i, j))
  have b := (hke i j s hs hl him).trans (period_growth_mono_bound ‖s‖ (Ce i j) (ke i j) K hx hk)
  rw [max_eq_left (hCe i j)] at b
  have hle : Ce i j ≤ ∑ i, ∑ j, Ce i j :=
    (Finset.single_le_sum (f := fun j => Ce i j) (fun j _ => hCe i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, Ce i j) (fun i _ => Finset.sum_nonneg fun j _ => hCe i j) (Finset.mem_univ i))
  exact b.trans (mul_le_mul_of_nonneg_right hle hP)

end GlobalTheory
