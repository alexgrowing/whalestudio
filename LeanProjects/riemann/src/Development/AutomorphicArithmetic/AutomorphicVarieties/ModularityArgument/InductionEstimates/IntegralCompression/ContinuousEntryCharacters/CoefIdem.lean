import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem chi_mul_neg (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi ν θ * chi ν (-θ) = 1 := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  simp

private theorem chi_mul_conj (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi ν θ * conj (chi ν θ) = 1 := by
  have h : conj (chi ν θ) = chi ν (-θ) := by
    unfold chi
    rw [← Complex.exp_conj, map_mul, map_sum, Complex.conj_I]
    congr 1
    simp only [map_mul, map_intCast, Complex.conj_ofReal, Pi.neg_apply, Complex.ofReal_neg, mul_neg, neg_mul,
      Finset.sum_neg_distrib]
  rw [h, chi_mul_neg]

private theorem int_zero {μ : Measure U4} (hH : Haar4 μ) {ν ν' : Fin (2 + 2) → ℤ} (hne : ν ≠ ν') (F : U4 → ℂ)
    (hF : ∀ θ h, chi ν' θ * F (dg θ * h) = chi ν θ * F h) : ∫ h, F h ∂μ = 0 := by
  obtain ⟨θ, hθ⟩ : ∃ θ, chi ν θ ≠ chi ν' θ := by
    by_contra hc
    push_neg at hc
    exact hne (u4.2.2.2.2.2.2.2.2.2.2.1 ν ν' hc)
  have hT : ∫ h, F (dg θ * h) ∂μ = ∫ h, F h ∂μ :=
    (hH.left (dg θ)).integral_comp (Homeomorph.mulLeft (dg θ)).measurableEmbedding F
  have h1 : chi ν' θ * ∫ h, F h ∂μ = chi ν θ * ∫ h, F h ∂μ :=
    calc chi ν' θ * ∫ h, F h ∂μ = chi ν' θ * ∫ h, F (dg θ * h) ∂μ := by rw [hT]
      _ = ∫ h, chi ν' θ * F (dg θ * h) ∂μ := (integral_const_mul _ _).symm
      _ = ∫ h, chi ν θ * F h ∂μ := integral_congr_ae (Eventually.of_forall fun h => hF θ h)
      _ = chi ν θ * ∫ h, F h ∂μ := integral_const_mul _ _
  have h2 : (chi ν θ - chi ν' θ) * ∫ h, F h ∂μ = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hθ)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefIdem :
    ∀ (μ : Measure U4) ψ n q n' q', Haar4 μ → μ.IsOpenPosMeasure → Coef ψ n q n' q' → Continuous ψ ∧ ψ 1 = 1 ∧ Idem μ (eOf μ ψ) ∧ RFix μ (eOf μ ψ) ψ := by
  intro μ ψ n q n' q' hH hO hC
  haveI : CompactSpace U4 := u4.2.2.2.2.2.2.2.2.2.2.2.1
  haveI : IsProbabilityMeasure μ := hH.prob
  obtain ⟨J, _, j₀, a, b, ν, hcont, hexp, ha0, hb0, hν0, hw, -, hne⟩ := hC.exp
  have hψc : Continuous ψ := ha0 ▸ (hcont j₀).1
  have hψ1 : ψ 1 = 1 := by
    have h := hC.res 1 1
    rw [u4.2.2.1, KT.psi_one, KT.psi_one, mul_one] at h
    exact h
  have hint : ∀ f : U4 → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hinv : Continuous fun h : U4 => h⁻¹ := continuous_inv
  have hψdg : ∀ θ h, ψ (dg θ * h) = chi (wt n q n' q') θ * ψ h := fun θ h => by
    have := (hw j₀ θ h).2.1
    rwa [ha0] at this
  set c : ℝ := ∫ h, ‖ψ h‖ ^ 2 ∂μ with hc
  have hcpos : 0 < c := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : U4)) (by fun_prop)
      (HasCompactSupport.of_compactSpace _) (fun _ => by positivity) ?_
    simp [hψ1]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hmc : ∀ h, ψ h * conj (ψ h) = ((‖ψ h‖ ^ 2 : ℝ) : ℂ) := fun h => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcC : ∫ h, ψ h * conj (ψ h) ∂μ = (c : ℂ) := by
    simp_rw [hmc]
    exact integral_complex_ofReal
  have key1 : ∀ k, ∫ h, ψ h * ψ (h⁻¹ * k) ∂μ = c * ψ k := fun k => by
    have e1 : ∀ h, ψ h * ψ (h⁻¹ * k) = ∑ j, (ψ h * a j h⁻¹) * b j k := fun h => by
      rw [hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
    simp_rw [e1]
    rw [integral_finset_sum (μ := μ) Finset.univ (f := fun j h => ψ h * a j h⁻¹ * b j k) fun j _ =>
      hint _ ((hψc.mul ((hcont j).1.comp hinv)).mul continuous_const)]
    simp_rw [integral_mul_const]
    rw [Finset.sum_eq_single j₀]
    · rw [ha0, hb0]
      congr 1
      rw [← hcC]
      exact integral_congr_ae (Eventually.of_forall fun h => by
        show ψ h * ψ h⁻¹ = ψ h * conj (ψ h)
        rw [hC.star])
    · intro j _ hj
      rw [int_zero hH (ν := wt n q n' q') (ν' := ν j) (Ne.symm (hν0 ▸ hne j hj)) _ ?_, zero_mul]
      intro θ h
      rw [_root_.mul_inv_rev, u4.2.2.2.2.2.2.2.2.2.1, hψdg, (hw j (-θ) h⁻¹).1]
      have := chi_mul_neg (ν j) θ
      linear_combination (chi (wt n q n' q') θ * ψ h * a j h⁻¹) * this
    · intro h
      exact absurd (Finset.mem_univ _) h
  have key2 : ∀ g, ∫ k, conj (ψ k) * ψ (g * k) ∂μ = c * ψ g := fun g => by
    have e1 : ∀ k, conj (ψ k) * ψ (g * k) = ∑ j, a j g * (conj (ψ k) * b j k) := fun k => by
      rw [hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e1]
    rw [integral_finset_sum (μ := μ) Finset.univ (f := fun j k => a j g * (conj (ψ k) * b j k)) fun j _ =>
      hint _ (continuous_const.mul ((Complex.continuous_conj.comp hψc).mul (hcont j).2))]
    simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single j₀]
    · rw [ha0, hb0, mul_comm]
      congr 1
      rw [← hcC]
      exact integral_congr_ae (Eventually.of_forall fun h => mul_comm _ _)
    · intro j _ hj
      rw [int_zero hH (ν := ν j) (ν' := wt n q n' q') (hν0 ▸ hne j hj) _ ?_, mul_zero]
      intro θ k
      rw [hψdg, (hw j θ k).2.2, map_mul]
      have := chi_mul_conj (wt n q n' q') θ
      linear_combination (conj (ψ k) * chi (ν j) θ * b j k) * this
    · intro h
      exact absurd (Finset.mem_univ _) h
  have heOf : ∀ k, eOf μ ψ k = (c : ℂ)⁻¹ * conj (ψ k) := fun k => rfl
  refine ⟨hψc, hψ1, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact continuous_const.mul (Complex.continuous_conj.comp hψc)
  · intro k
    rw [heOf, heOf, hC.star, map_mul, map_inv₀, Complex.conj_ofReal]
  · intro k
    have e1 : ∀ h, eOf μ ψ h * eOf μ ψ (h⁻¹ * k) = ((c : ℂ)⁻¹ * (c : ℂ)⁻¹) * conj (ψ h * ψ (h⁻¹ * k)) := fun h => by
      rw [heOf, heOf, map_mul]
      ring
    simp_rw [e1]
    rw [integral_const_mul, integral_conj, key1, heOf, map_mul, Complex.conj_ofReal]
    field_simp
  · intro g
    have e1 : ∀ k, eOf μ ψ k * ψ (g * k) = (c : ℂ)⁻¹ * (conj (ψ k) * ψ (g * k)) := fun k => by
      rw [heOf, mul_assoc]
    simp_rw [e1]
    rw [integral_const_mul, key2]
    field_simp
