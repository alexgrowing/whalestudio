import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitianStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitianStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydiscStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImRealCombinationEqDotProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRealCombinationsOfIndependentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthOfSpanningCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthMatrixMulBoundedVectorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerGrowth

theorem differentiableOn_matrix_det_of_entries_normedSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B) :
    DifferentiableOn ℂ (fun b => (A b).det) B := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  have key : ∀ t : Finset (Fin d), DifferentiableOn ℂ (fun b => ∏ i ∈ t, A b (σ i) i) B := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).mul ih
  exact key _

theorem differentiableOn_matrix_inv_apply_of_entries {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B)
    (hd : ∀ b ∈ B, (A b).det ≠ 0) (i j : Fin d) :
    DifferentiableOn ℂ (fun b => (A b)⁻¹ i j) B := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((differentiableOn_matrix_det_of_entries_normedSpace hA).inv hd).mul (differentiableOn_matrix_det_of_entries_normedSpace fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableOn_const _
  · exact hA _ _

theorem lam_polyGrowth_of_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a g r lam M W hd hs hW hb
  by_cases hne : (logDom n a).Nonempty
  swap
  · exact ⟨0, 0, fun s hs' => absurd ⟨s, hs'⟩ hne⟩
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hli0, hsp0, Hm0, hH0, hP0, hM0⟩ := hs s0 hs0
  obtain ⟨hMa, hMd, hr⟩ := GlobalTheory.T.hermForm_periods_alternating_nondeg_rank_eq_two_mul g r (lam s0) M Hm0 hli0 hsp0 hH0 hP0 hM0
  obtain ⟨d, e, f, heW, hee, hfe, hsp⟩ := GlobalTheory.T.exists_lagrangian_dual_pair_in_coisotropic r M W hMa hMd hW
  obtain ⟨hli, hrd⟩ := GlobalTheory.T.isotropicDual_family_linearIndependent_rank_eq_two_mul r d M e f hee hfe hsp
  obtain rfl : d = g := by omega
  obtain ⟨E, hE⟩ : ∃ E : (Fin n → ℂ) → Fin d → Fin d → ℂ, E = fun s i => ∑ m, (e i m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℂ) → Fin d → Fin d → ℂ, F = fun s j => ∑ m, (f j m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨Em, hEm⟩ : ∃ Em : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Em = fun s => Matrix.of fun k i => E s i k :=
    ⟨_, rfl⟩
  obtain ⟨Fm, hFm⟩ : ∃ Fm : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Fm = fun s => Matrix.of fun k j => F s j k :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : (Fin n → ℂ) → Fin d → Fin d → ℂ, τ = fun s i j => ((Em s)⁻¹ * Fm s) i j := ⟨_, rfl⟩
  have hlinE : LinearIndependent ℝ e := hli.comp Sum.inl Sum.inl_injective

  have hpt : ∀ s ∈ logDom n a, (Em s).det ≠ 0 ∧ (∀ j, F s j = ∑ i, τ s i j • E s i) ∧
      (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) ∧
      ∀ i j, τ s i j - τ s j i = ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ) := by
    intro s hs'
    obtain ⟨hli1, -, Hm, hH, hP, hMs⟩ := hs s hs'
    have h6 := GlobalTheory.T.hermForm_im_real_combination_eq_dotProduct d r (lam s) M Hm hMs
    have hEE : ∀ i j, (hermForm Hm (E s i) (E s j)).im = 0 := fun i j => by
      rw [hE]; exact (h6 _ _).trans (hee i j)
    have hFE : ∀ i j, (hermForm Hm (F s i) (E s j)).im = if i = j then 1 else 0 := fun i j => by
      rw [hE, hF]; exact (h6 _ _).trans (hfe i j)
    have hFF : ∀ i j, (hermForm Hm (F s i) (F s j)).im = f i ⬝ᵥ M *ᵥ f j := fun i j => by
      rw [hF]; exact h6 _ _
    have hEli : LinearIndependent ℝ (E s) := by
      rw [hE]; exact GlobalTheory.T.linearIndependent_real_combinations_of_independent d r d (lam s) e hli1 hlinE
    have hdet : (Em s).det ≠ 0 := by rw [hEm]; exact GlobalTheory.T.det_ne_zero_of_real_independent_isotropic_hermitian d Hm (E s) hP hEli hEE
    have hFt : ∀ j, F s j = ∑ i, τ s i j • E s i := by
      intro j
      have hm := Matrix.mul_nonsing_inv_cancel_left (Em s) (Fm s) (Ne.isUnit hdet)
      funext k
      have := congrFun (congrFun hm k) j
      have hEmk : ∀ k i, Em s k i = E s i k := fun k i => by simp [hEm]
      have hFmk : ∀ k i, Fm s k i = F s i k := fun k i => by simp [hFm]
      rw [Matrix.mul_apply] at this
      simp only [hEmk, hFmk] at this
      rw [hτ]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    obtain ⟨h4a, h4b⟩ := GlobalTheory.T.riemann_relations_period_matrix_hermitian d d Hm (E s) (F s) (τ s) hH hP hFt hEE hFE
    exact ⟨hdet, hFt, h4a, fun i j => (h4b i j).trans (by rw [hFF])⟩

  have hlam : ∀ m k, DifferentiableOn ℂ (fun s => lam s m k) (logDom n a) := fun m k =>
    differentiableOn_pi.1 (differentiableOn_pi.1 hd m) k
  have hEmd : ∀ k i, DifferentiableOn ℂ (fun s => Em s k i) (logDom n a) := fun k i => by
    simp only [hEm, hE, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hFmd : ∀ k i, DifferentiableOn ℂ (fun s => Fm s k i) (logDom n a) := fun k i => by
    simp only [hFm, hF, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hτd : DifferentiableOn ℂ τ (logDom n a) := by
    refine differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => ?_
    simp only [hτ, Matrix.mul_apply]
    exact DifferentiableOn.fun_sum fun l _ =>
      (differentiableOn_matrix_inv_apply_of_entries hEmd (fun s hs' => (hpt s hs').1) i l).mul (hFmd l j)
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.periodMatrix_polynomialGrowth_puncturedPolydisc n a d τ (fun i j => ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ)) hτd (fun s hs' => (hpt s hs').2.2.1)
    (fun s hs' => (hpt s hs').2.2.2)
  set R : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ ‖logExp a s‖ ≤ 1 / 2 ∧
    ∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi} with hR
  have hEb : ∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C := fun i => by
    obtain ⟨C, hC⟩ := hb (e i) (heW i)
    exact ⟨C, fun s hs' => by rw [hE]; exact hC s hs'.1 hs'.2.1⟩
  have h9 := GlobalTheory.T.polynomial_growth_matrix_mul_bounded_vectors n d d R τ E ⟨C, k, fun s hs' => hC s hs'.1 hs'.2.1 hs'.2.2⟩ hEb
  obtain ⟨C', k', h8⟩ := GlobalTheory.T.polynomial_growth_of_spanning_combinations n d r (Fin d ⊕ Fin d) R lam (Sum.elim e f) hsp (fun i => by
    rcases i with i | j
    · obtain ⟨C, hC⟩ := hEb i
      exact ⟨C, 0, fun s hs' => by simpa [hE] using hC s hs'⟩
    · obtain ⟨C, k, hC⟩ := h9 j
      refine ⟨C, k, fun s hs' => ?_⟩
      have := (hpt s hs'.1).2.1 j
      simp only [hF] at this
      simp only [Sum.elim_inr]
      rw [this]
      exact hC s hs')
  exact ⟨C', k', fun s hs' h1 h2 => h8 s ⟨hs', h1, h2⟩⟩

end GlobalTheory.ShFam.Hor.LogCh.PerGrowth
