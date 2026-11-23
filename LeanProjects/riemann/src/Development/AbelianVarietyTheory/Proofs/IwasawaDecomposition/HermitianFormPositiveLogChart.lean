import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydisc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImaginaryPeriodLowerBoundLogStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicPeriodMatrixStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormPeriodLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientBoundPeriodBasisStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder

namespace GlobalTheory.PerCmp

theorem exists_symplectic_basis_coords : ∀ (g r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ), Mᵀ = -M → M.det ≠ 0 → r = 2 * g → ∃ (e f : Fin g → Fin r → ℝ) (P Q : Fin r → Fin g → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ LinearIndependent ℝ e ∧ ∀ m, (Pi.single m 1 : Fin r → ℝ) = ∑ k, P m k • e k + ∑ k, Q m k • f k := by
  intro g r M hanti hdet hr
  obtain ⟨d, e, f, -, hee, hfe, hsp⟩ :=
    exists_lagrangian_dual_in_coisotropic r M ⊤ hanti hdet (fun v _ => Submodule.mem_top)
  obtain ⟨hli, hrd⟩ := familyIsotropicDual_linearIndependent_and_card r d M e f hee hfe hsp
  obtain rfl : d = g := by omega
  have hex : ∀ m : Fin r, ∃ c : Fin d ⊕ Fin d → ℝ, ∑ i, c i • Sum.elim e f i = Pi.single m 1 :=
    fun m => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hsp ▸ Submodule.mem_top)
  choose c hc using hex
  refine ⟨e, f, fun m k => c m (Sum.inl k), fun m k => c m (Sum.inr k), hee, hfe, ?_, fun m => ?_⟩
  · simpa using hli.comp Sum.inl Sum.inl_injective
  · rw [← hc m, Fintype.sum_sum_type]
    simp

end GlobalTheory.PerCmp

set_option maxHeartbeats 1000000 in
open GlobalTheory.PerCmp in

theorem GlobalTheory.hermForm_norm_comparison_of_periods : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), DifferentiableOn ℂ lam (logDom n a) → (∀ t ∈ logDom n a, LinearIndependent ℝ (lam t) ∧ Submodule.span ℝ (Set.range (lam t)) = ⊤ ∧ (Hm t).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) z z).re) ∧ (∀ i i', (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) (lam t i) (lam t i')).im = M i i') ∧ ∀ i, ∑ m, ρ i m • lam t m = Pi.single i 1) → (∃ (C : ℝ) (k : ℕ), ∀ t ∈ logDom n a, ‖logExp a t‖ ≤ 1 / 2 → (∀ i : Fin n, (i : ℕ) < a → |(t i).im| ≤ Real.pi) → ‖lam t‖ ≤ C * (1 + ‖t‖) ^ k) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ t ∈ logDom n a, ‖logExp a t‖ ≤ 1 / 2 → (∀ i : Fin n, (i : ℕ) < a → |(t i).im| ≤ Real.pi) → ∀ w : Fin g → ℂ, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) w w).re ≤ C * (1 + ‖t‖) ^ k * ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ C * (1 + ‖t‖) ^ k * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) w w).re := by
  intro n a g r lam ρ M Hm hlam hpt hgrow
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀def
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq, hs₀def]
    intro k; split_ifs <;> norm_num
  obtain ⟨hli₀, hsp₀, hH₀, hpos₀, hM₀, -⟩ := hpt s₀ hs₀
  obtain ⟨hanti, hdet, hr⟩ := hermForm_periods_alternating_nondeg g r (lam s₀) M (Hm s₀) hli₀ hsp₀ hH₀ hpos₀ hM₀
  obtain ⟨e, f, P, Q, hee, hfe, heli, hPQ⟩ := exists_symplectic_basis_coords g r M hanti hdet hr

  have hImExp : ∀ t ∈ logDom n a, ∀ x y : Fin r → ℝ,
      (hermForm (Hm t) (∑ m, (x m : ℂ) • lam t m) (∑ m, (y m : ℂ) • lam t m)).im = x ⬝ᵥ M *ᵥ y := by
    intro t ht x y
    obtain ⟨-, -, -, -, hM, -⟩ := hpt t ht
    have hc : ∀ (z : Fin r → ℝ), (∑ m, (z m : ℂ) • lam t m) = ∑ m, z m • lam t m := fun z =>
      Finset.sum_congr rfl fun m _ => (Complex.coe_smul _ _)
    rw [hc, hc]
    show hermFormImBilin (Hm t) _ _ = _
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    have hb : ∀ u w, hermFormImBilin (Hm t) u w = (hermForm (Hm t) u w).im := fun _ _ => rfl
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    simp only [hb, hM]; ring

  set E : (Fin n → ℂ) → Fin g → Fin g → ℂ := fun t i => ∑ m, ((e i m : ℝ) : ℂ) • lam t m with hEdef
  set F : (Fin n → ℂ) → Fin g → Fin g → ℂ := fun t i => ∑ m, ((f i m : ℝ) : ℂ) • lam t m with hFdef
  have hlm : ∀ m, DifferentiableOn ℂ (fun t => lam t m) (logDom n a) := fun m => differentiableOn_pi.1 hlam m
  have hEd : DifferentiableOn ℂ E (logDom n a) :=
    differentiableOn_pi.2 fun i => DifferentiableOn.fun_sum fun m _ => by have := hlm m; fun_prop
  have hFd : DifferentiableOn ℂ F (logDom n a) :=
    differentiableOn_pi.2 fun i => DifferentiableOn.fun_sum fun m _ => by have := hlm m; fun_prop
  have hEE : ∀ t ∈ logDom n a, ∀ i j, (hermForm (Hm t) (E t i) (E t j)).im = 0 := fun t ht i j => by
    rw [hImExp t ht]; exact hee i j
  have hFE : ∀ t ∈ logDom n a, ∀ i j, (hermForm (Hm t) (F t i) (E t j)).im = if i = j then 1 else 0 :=
    fun t ht i j => by rw [hImExp t ht]; exact hfe i j
  have hFF : ∀ t ∈ logDom n a, ∀ i j, (hermForm (Hm t) (F t i) (F t j)).im = f i ⬝ᵥ M *ᵥ f j :=
    fun t ht i j => hImExp t ht _ _
  have hEli : ∀ t ∈ logDom n a, LinearIndependent ℝ (E t) := by
    intro t ht
    obtain ⟨hli, -⟩ := hpt t ht
    rw [Fintype.linearIndependent_iff] at hli heli ⊢
    intro c hc
    have h1 : ∑ m, (∑ i, c i * e i m) • lam t m = 0 := by
      rw [← hc]
      simp only [hEdef, Finset.smul_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.coe_smul, smul_smul]
    have h2 := hli _ h1
    apply heli c
    funext m
    simpa [Finset.sum_apply] using h2 m
  have hdetE : ∀ t ∈ logDom n a, (Matrix.of fun k i => E t i k).det ≠ 0 := fun t ht =>
    det_ne_zero_of_real_indep_isotropic g (Hm t) (E t) (hpt t ht).2.2.2.1 (hEli t ht) (hEE t ht)
  obtain ⟨τ, hτd, hτ⟩ := GlobalTheory.T.exists_holomorphic_period_matrix n g (logDom n a) E F hEd hFd hdetE
  have hRR : ∀ t ∈ logDom n a, _ := fun t ht =>
    riemann_relations_period_matrix g g (Hm t) (E t) (F t) (τ t) (hpt t ht).2.2.1 (hpt t ht).2.2.2.1
      (hτ t ht) (hEE t ht) (hFE t ht)
  obtain ⟨Cτ, kτ, hCτ⟩ := period_matrix_polynomial_growth n a g τ (fun i j => ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ)) hτd
    (fun t ht => (hRR t ht).1) (fun t ht i j => by rw [(hRR t ht).2 i j, hFF t ht])
  obtain ⟨c₁, k₁, hc₁, hlow⟩ := GlobalTheory.T.imaginary_period_lower_bound_log n a g τ hτd (fun t ht => (hRR t ht).1)
  obtain ⟨Cl, kl, hCl⟩ := hgrow
  have hlamPQ : ∀ t, ∀ m, lam t m = ∑ k, (P m k : ℂ) • E t k + ∑ k, (Q m k : ℂ) • F t k := by
    intro t m
    have h := fun m' => congrFun (hPQ m) m'
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [hEdef, hFdef, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun k m' => ((Q m k : ℂ) * (f k m' : ℂ)) • lam t m'), ← Finset.sum_add_distrib]
    simp only [← Finset.sum_smul, ← add_smul]
    have h' : ∀ m', (∑ k, (P m k : ℂ) * (e k m' : ℂ) + ∑ k, (Q m k : ℂ) * (f k m' : ℂ)) = ((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℂ) := by
      intro m'; rw [h m']; push_cast; rfl
    simp only [h']
    simp [Pi.single_apply]

  set Cτ' := max Cτ 0 with hCτ'
  set Cl' := max Cl 0 with hCl'
  have hEn : ∀ t k, ‖E t k‖ ≤ r * ‖e‖ * ‖lam t‖ := by
    intro t k
    refine (norm_sum_le _ _).trans ?_
    have : ∀ m ∈ Finset.univ, ‖((e k m : ℝ) : ℂ) • lam t m‖ ≤ ‖e‖ * ‖lam t‖ := by
      intro m _
      rw [norm_smul, Complex.norm_real]
      exact mul_le_mul ((norm_le_pi_norm (e k) m).trans (norm_le_pi_norm e k)) (norm_le_pi_norm (lam t) m)
        (norm_nonneg _) (norm_nonneg _)
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    simp [mul_assoc]
  set X : ℝ := (g : ℝ) * ((r : ℝ) * ‖ρ‖ * (‖P‖ + (g : ℝ) * ‖Q‖ * Cτ')) with hX
  set B : ℝ := (r : ℝ) * ‖e‖ * Cl' with hB
  have hX0 : 0 ≤ X := by positivity
  have hB0 : 0 ≤ B := by positivity
  set KU : ℝ := 2 * (g : ℝ) ^ 2 * X ^ 2 / c₁ with hKU
  set KL : ℝ := ((g : ℝ) * B) ^ 2 * ((g : ℝ) * Cτ') ^ 2 / c₁ with hKL
  have hKU0 : 0 ≤ KU := by positivity
  have hKL0 : 0 ≤ KL := by positivity
  refine ⟨KU + KL, k₁ + 2 * kτ + 2 * kl, by positivity, ?_⟩
  intro t ht hle him w
  set p : ℝ := 1 + ‖t‖ with hp
  have hp1 : 1 ≤ p := by have := norm_nonneg t; linarith
  have hp0 : 0 ≤ p := by linarith
  have hpk : ∀ j, j ≤ k₁ + 2 * kτ + 2 * kl → p ^ j ≤ p ^ (k₁ + 2 * kτ + 2 * kl) :=
    fun j hj => pow_le_pow_right₀ hp1 hj
  have hτt : ‖τ t‖ ≤ Cτ' * p ^ kτ :=
    (hCτ t ht hle him).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hlt : ‖lam t‖ ≤ Cl' * p ^ kl :=
    (hCl t ht hle him).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hCτ0 : 0 ≤ Cτ' := le_max_right _ _
  have hCl0 : 0 ≤ Cl' := le_max_right _ _
  obtain ⟨av, hw, ha⟩ := GlobalTheory.T.coefficient_bound_period_basis g r (lam t) ρ (E t) (F t) (τ t) P Q (hlamPQ t) (hτ t ht) (hpt t ht).2.2.2.2.2 w
  obtain ⟨h1, h2⟩ := GlobalTheory.T.hermitian_form_period_lower_bound g (Hm t) (E t) (F t) (τ t) c₁ (p ^ k₁) (Cτ' * p ^ kτ) (hpt t ht).2.2.1 (hpt t ht).2.2.2.1
    (hτ t ht) (hEE t ht) (hFE t ht) hc₁ (fun v => hlow t ht hle v) hτt av
  rw [← hw] at h1 h2
  set H := (hermForm (Hm t) w w).re with hH
  have hH0 : 0 ≤ H := by
    by_cases hw0 : w = 0
    · simp [hH, hw0, hermForm]
    · exact ((hpt t ht).2.2.2.1 w hw0).le
  have hA : ‖av‖ ≤ X * p ^ kτ * ‖w‖ := by
    refine ha.trans ?_
    have hin : ‖P‖ + (g : ℝ) * ‖Q‖ * ‖τ t‖ ≤ (‖P‖ + (g : ℝ) * ‖Q‖ * Cτ') * p ^ kτ := by
      have hp' : 1 ≤ p ^ kτ := one_le_pow₀ hp1
      have e1 : ‖P‖ ≤ ‖P‖ * p ^ kτ := le_mul_of_one_le_right (norm_nonneg _) hp'
      have e2 : (g : ℝ) * ‖Q‖ * ‖τ t‖ ≤ (g : ℝ) * ‖Q‖ * (Cτ' * p ^ kτ) :=
        mul_le_mul_of_nonneg_left hτt (by positivity)
      nlinarith
    have hw0 := norm_nonneg w
    calc (g : ℝ) * ((r : ℝ) * ‖ρ‖ * (‖P‖ + (g : ℝ) * ‖Q‖ * ‖τ t‖)) * ‖w‖
        ≤ (g : ℝ) * ((r : ℝ) * ‖ρ‖ * ((‖P‖ + (g : ℝ) * ‖Q‖ * Cτ') * p ^ kτ)) * ‖w‖ := by gcongr
      _ = X * p ^ kτ * ‖w‖ := by rw [hX]; ring
  have hW : ‖w‖ ≤ g * ‖av‖ * (B * p ^ kl) := by
    rw [hw]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.univ, ‖av k • E t k‖ ≤ ‖av‖ * (B * p ^ kl) := by
      intro k _
      rw [norm_smul]
      refine mul_le_mul (norm_le_pi_norm av k) ((hEn t k).trans ?_) (norm_nonneg _) (norm_nonneg _)
      have h3 : (r : ℝ) * ‖e‖ * ‖lam t‖ ≤ (r : ℝ) * ‖e‖ * (Cl' * p ^ kl) :=
        mul_le_mul_of_nonneg_left hlt (by positivity)
      calc (r : ℝ) * ‖e‖ * ‖lam t‖ ≤ (r : ℝ) * ‖e‖ * (Cl' * p ^ kl) := h3
        _ = B * p ^ kl := by rw [hB]; ring
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  constructor
  ·
    have hc : c₁ * KU = 2 * (g : ℝ) ^ 2 * X ^ 2 := by rw [hKU]; field_simp
    have hA2 : ‖av‖ ^ 2 ≤ X ^ 2 * p ^ (2 * kτ) * ‖w‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hA 2
      calc ‖av‖ ^ 2 ≤ (X * p ^ kτ * ‖w‖) ^ 2 := this
        _ = X ^ 2 * p ^ (2 * kτ) * ‖w‖ ^ 2 := by ring
    have hmain : c₁ * H ≤ c₁ * (KU * p ^ (k₁ + 2 * kτ + 2 * kl) * ‖w‖ ^ 2) := by
      calc c₁ * H ≤ 2 * (g : ℝ) ^ 2 * p ^ k₁ * ‖av‖ ^ 2 := h2
        _ ≤ 2 * (g : ℝ) ^ 2 * p ^ k₁ * (X ^ 2 * p ^ (2 * kτ) * ‖w‖ ^ 2) := by gcongr
        _ = 2 * (g : ℝ) ^ 2 * X ^ 2 * p ^ (k₁ + 2 * kτ) * ‖w‖ ^ 2 := by ring
        _ ≤ 2 * (g : ℝ) ^ 2 * X ^ 2 * p ^ (k₁ + 2 * kτ + 2 * kl) * ‖w‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpk _ (by omega)) (by positivity)) (by positivity)
        _ = c₁ * (KU * p ^ (k₁ + 2 * kτ + 2 * kl) * ‖w‖ ^ 2) := by rw [← hc]; ring
    have := le_of_mul_le_mul_left hmain hc₁
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
  ·
    have hc : c₁ * KL = ((g : ℝ) * B) ^ 2 * ((g : ℝ) * Cτ') ^ 2 := by rw [hKL]; field_simp
    have hW2 : ‖w‖ ^ 2 ≤ ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * ‖av‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hW 2
      calc ‖w‖ ^ 2 ≤ (g * ‖av‖ * (B * p ^ kl)) ^ 2 := this
        _ = ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * ‖av‖ ^ 2 := by ring
    have hmain : c₁ * ‖w‖ ^ 2 ≤ c₁ * (KL * p ^ (k₁ + 2 * kτ + 2 * kl) * H) := by
      calc c₁ * ‖w‖ ^ 2 ≤ ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * (c₁ * ‖av‖ ^ 2) := by
            nlinarith [hW2, hc₁]
        _ ≤ ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * (p ^ k₁ * ((g : ℝ) * (Cτ' * p ^ kτ)) ^ 2 * H) := by gcongr
        _ = ((g : ℝ) * B) ^ 2 * ((g : ℝ) * Cτ') ^ 2 * p ^ (k₁ + 2 * kτ + 2 * kl) * H := by ring
        _ = c₁ * (KL * p ^ (k₁ + 2 * kτ + 2 * kl) * H) := by rw [← hc]; ring
    have := le_of_mul_le_mul_left hmain hc₁
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
