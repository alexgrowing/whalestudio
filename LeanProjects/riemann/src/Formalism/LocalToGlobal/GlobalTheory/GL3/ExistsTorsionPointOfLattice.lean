import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.ConjugateTorsionPointExists
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.LambdaConjLatticeUniform
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.TwoTorsionOffKernelsExists
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.ThetaTranslationOperatorApply
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical Formalism.MainNotions
open Formalism.L2.Th1 (F2.IsLat F2.HasCM)

theorem first_integral_eq (Λ : AddSubgroup ℂ) (ω : ℂ) (G : ℂ → ℂ) : PI.U1 Λ ω G = Formalism.MainNotions.TaylorLogMetric.U1 Λ ω G := rfl

theorem sgStar_spec (L : PeriodPair) :
    Differentiable ℂ (Formalism.L2.Th1.F.sgStar L) ∧ deriv (Formalism.L2.Th1.F.sgStar L) 0 = 1 ∧
      (∀ z, Formalism.L2.Th1.F.sgStar L (-z) = -Formalism.L2.Th1.F.sgStar L z) ∧
      ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω (Formalism.L2.Th1.F.sgStar L) z =
        (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * Formalism.L2.Th1.F.sgStar L z := by
  obtain ⟨h1, h2, -, h4, -⟩ := Formalism.L2.Th1.F.sgStarBasic L
  refine ⟨h1, h4, h2, fun ω hω z => ?_⟩
  rw [Formalism.L2.GlobalTheoryTheory.taylorLogMetric_U1_eq_U1, Formalism.L2.Th1.F2.thetaTranslationOperator_apply]
  have hfix := Formalism.L2.Th1.F.sgStarFixed L ω z hω
  by_cases h : ω / 2 ∈ L.lattice
  · have hs : Formalism.L2.Th1.F.semiChar L ω = 1 := by unfold Formalism.L2.Th1.F.semiChar; simp [h]
    have h' : ω / 2 ∈ L.lattice.toAddSubgroup := h
    rw [if_pos h', one_mul, ← hfix, hs, one_mul]
  · have hs : Formalism.L2.Th1.F.semiChar L ω = -1 := by unfold Formalism.L2.Th1.F.semiChar; simp [h]
    have h' : ω / 2 ∉ L.lattice.toAddSubgroup := h
    rw [if_neg h', ← hfix, hs]
    ring

theorem sgStar_eq (L : PeriodPair) : Formalism.MainNotions.TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  have hlat : L.lattice.toAddSubgroup = PI.lat2 L.ω₁ L.ω₂ := Submodule.span_int_eq_addSubgroupClosure _
  have hIm : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
    have := Formalism.L2.Th1.F.areaPos L
    unfold Formalism.L2.Th1.F.area at this
    exact abs_pos.mp this
  have hF := sgStar_spec L
  have hE := Classical.epsilon_spec (p := fun G : ℂ → ℂ => Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
    ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G z =
      (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G z) ⟨_, hF⟩
  have huniq : ∀ G G' : ℂ → ℂ,
      (Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
        ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G z =
          (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G z) →
      (Differentiable ℂ G' ∧ deriv G' 0 = 1 ∧ (∀ z, G' (-z) = -G' z) ∧
        ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G' z =
          (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G' z) → G = G' := by
    intro G G' hG hG'
    rw [hlat] at hG hG'
    exact sigma_star_unique L.ω₁ L.ω₂ hIm G G' hG hG'
  unfold Formalism.MainNotions.TaylorLogMetric.sgStar
  exact huniq _ _ hE hF

theorem thetaZero_periodLattice_eq (L : PeriodPair) (t : ℂ) : GL3Theta.th0 L.lattice.toAddSubgroup t = Formalism.L2.Th1.F.th0 L t := by
  funext z
  unfold GL3Theta.th0 Formalism.L2.Th1.F.th0
  rw [sgStar_eq, Formalism.L2.GlobalTheoryTheory.taylorLogMetric_U1_eq_U1, Formalism.L2.Th1.F2.thetaTranslationOperator_apply, Formalism.L2.Th1.F2.thetaTranslationOperator_apply]

theorem cmTheta_eq (d : ℕ) : Formalism.L2.Th1.F.cmTheta 1 d = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 := by
  unfold Formalism.L2.Th1.F.cmTheta
  push_cast
  ring

theorem one_sub_cmTheta_eq (d : ℕ) : 1 - Formalism.L2.Th1.F.cmTheta 1 d = (1 - Complex.I * (Real.sqrt d : ℂ)) / 2 := by
  rw [cmTheta_eq]
  ring

theorem is_theta_at_torsion_point (D : D7) (Λ : AddSubgroup ℂ) (hL : F2.IsLat Λ) (hCM : F2.HasCM D.host.d Λ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D Λ t0) : GL3Theta.IsTheta0 D.host.d Λ (GL3Theta.th0 Λ t0) := by
  obtain ⟨L, rfl⟩ := hL
  rw [Formalism.L2.GlobalTheoryTheory.is_theta_zero_iff, thetaZero_periodLattice_eq]
  have hd : D.host.d % 8 = 7 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨h2, h3, h4⟩ := ht
  have e2 : 2 * t0 / 2 = t0 := by ring
  have h := Formalism.L2.Th1.F2.theta_zero_witness_holds D.host.d L (2 * t0) hd hCM h2
    (by rw [e2, cmTheta_eq]; exact h3) (by rw [e2, one_sub_cmTheta_eq]; exact h4)
  rwa [e2] at h

theorem exists_torsion_point_of_lattice (D : D7) (Λ : AddSubgroup ℂ) (hL : F2.IsLat Λ) : ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D Λ t0 := by
  obtain ⟨L, rfl⟩ := hL
  obtain ⟨ω₀, h0, h1, h2⟩ := Formalism.L2.Th1.F2.two_torsion_off_kernels_exists D.host.d L
  refine ⟨ω₀ / 2, ?_, ?_, ?_⟩
  · rw [show 2 * (ω₀ / 2) = ω₀ by ring]; exact h0
  · rw [← cmTheta_eq]; exact h1
  · rw [← one_sub_cmTheta_eq]; exact h2

variable [Fact _root_.Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.CMConjSetF] in
theorem conjugate_theta_values (D : D7) : ThetaConjugation D := by
  intro cc hcc δ hδ M _ hD ρ t0 ht
  obtain ⟨hL, hC⟩ := Formalism.L2.Th1.F2.lambda_conj_lattice_uniform D cc hcc δ hδ M hD ρ
  exact is_theta_at_torsion_point D _ hL hC t0 ht

variable [Fact _root_.Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.CMConjSetF] in
theorem conjugate_torsion_point_exists (D : D7) : ConjugateTorsionPointExists D := by
  intro cc hcc δ hδ M _ hD ρ
  exact exists_torsion_point_of_lattice D _ (Formalism.L2.Th1.F2.lambda_conj_lattice_uniform D cc hcc δ hδ M hD ρ).1

theorem genus_one_norm_sq_eq (Λ : AddSubgroup ℂ) (g : ℂ → ℂ) : StandardLatticesGL3.nrm1Sq Λ g = GL3Theta.normSq1 Λ g := by
  have h : ∀ z : ℂ, -Real.pi * ‖z‖ ^ 2 / Formalism.MainNotions.TaylorLogMetric.area Λ = -Real.pi * (GL3Theta.hf1 Λ z z).re := by
    intro z
    unfold GL3Theta.hf1
    rw [Complex.mul_conj, Complex.div_ofReal_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    ring
  unfold StandardLatticesGL3.nrm1Sq GL3Theta.normSq1
  simp only [h]

theorem v_ge (D : D7) : Real.sqrt ((D.host.q : ℝ) * D.host.d) / 2 ≤ D.host.v := by
  have h : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  unfold Host.v
  linarith

theorem q_ge (D : D7) : (3 : ℝ) ≤ D.host.q := by
  have hp := D.host.hyp.1
  have h8 := D.host.hyp.2.2.1
  have : 3 ≤ D.host.q := by have := hp.two_le; omega
  exact_mod_cast this

theorem d_ge (D : D7) : (7 : ℝ) ≤ D.host.d := by
  have h := D.host.hyp.2.2.2.1
  have : 7 ≤ D.host.d := by omega
  exact_mod_cast this

theorem one_le_v (D : D7) : 1 ≤ D.host.v := by
  have hv := v_ge D
  have hq := q_ge D
  have hd := d_ge D
  have h0 : (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by positivity
  have hs := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d)
  nlinarith

theorem sqrtDGammaLeLogV (D : D7) : SqrtDGammaLeLogV D := by
  unfold SqrtDGammaLeLogV
  have hq := q_ge D
  have hd := d_ge D
  have hv := v_ge D
  have hsd : 0 < Real.sqrt (D.host.d : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsq0 : 0 ≤ Real.sqrt (D.host.q : ℝ) := Real.sqrt_nonneg _
  have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ D.host.q by linarith)
  have hsq : (4 : ℝ) / 3 ≤ Real.sqrt (D.host.q : ℝ) := by nlinarith
  have hpos : 0 < Real.sqrt (D.host.q : ℝ) / 2 := by linarith
  have hm : Real.sqrt ((D.host.q : ℝ) * D.host.d) = Real.sqrt (D.host.q : ℝ) * Real.sqrt (D.host.d : ℝ) :=
    Real.sqrt_mul (by linarith) _
  have hlog : Real.log (Real.sqrt (D.host.q : ℝ) / 2 * Real.sqrt (D.host.d : ℝ)) ≤ Real.log D.host.v := by
    apply Real.log_le_log (by positivity)
    rw [hm] at hv
    linarith
  rw [Real.log_mul hpos.ne' hsd.ne'] at hlog
  have h1 := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : (Real.sqrt (D.host.q : ℝ) / 2)⁻¹ ≤ 3 / 2 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  linarith

variable [Fact _root_.Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.CMConjSetF] in
theorem link_conjugate_curves : LinkConjE := by
  intro D hn cc hcc δ hδ B χ ht N N' L₁ L₁' L₂ L₂' a₁ a₂ M _ hD c₁ c₂ ρ
  have : NumberField M := NumberField.mk
  obtain ⟨t0', ht0'⟩ := conjugate_torsion_point_exists D cc hcc δ hδ M hD ρ
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  rw [(hn cc δ hc _ B.t0 N N' L₁ L₁' (StandardLatticesGL3.admissible_self_dual_even a₁).1 (StandardLatticesGL3.admissible_self_dual_even a₁).2.1 (StandardLatticesGL3.admissible_self_dual_even a₁).2.2 _
      (ht _ B.t0 N N' L₁ L₁' a₁) M ρ hD c₁ t0' ht0').1,
    (hn cc δ hc _ B.t0 N N' L₂ L₂' (StandardLatticesGL3.admissible_self_dual_even a₂).1 (StandardLatticesGL3.admissible_self_dual_even a₂).2.1 (StandardLatticesGL3.admissible_self_dual_even a₂).2.2 _
      (ht _ B.t0 N N' L₂ L₂' a₂) M ρ hD c₂ t0' ht0').1]

variable [Fact _root_.Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.CMConjSetF] in
theorem link_mean_value : LinkMeanE := by
  intro D hn hm cc hcc δ hδ B χ ht C hC Lsc hL N N' L L' hA M _ hD hcoef
  have : NumberField M := NumberField.mk
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hex : ∀ ρ : M →ₐ[ℚ] ℂ, ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t :=
    conjugate_torsion_point_exists D cc hcc δ hδ M hD
  choose t0' ht0' using hex
  let G : (M →ₐ[ℚ] ℂ) → ℂ → ℂ := fun ρ => GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t0' ρ)
  have hG : ∀ ρ, GL3Theta.IsTheta0 D.host.d (lamConj M ρ (lamOf D cc δ)) (G ρ) :=
    fun ρ => conjugate_theta_values D cc hcc δ hδ M hD ρ _ (ht0' ρ)
  have hmean := hm cc δ hcc hδ M hD G hG
  have hnorm : ∀ ρ, normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
      (fnConj D M ρ (B.eNat χ N N' L L')) = GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (G ρ) ^ (fF D * N * N') := by
    intro ρ
    rw [(hn cc δ hc _ B.t0 N N' L L' (StandardLatticesGL3.admissible_self_dual_even hA).1 (StandardLatticesGL3.admissible_self_dual_even hA).2.1 (StandardLatticesGL3.admissible_self_dual_even hA).2.2 _
      (ht _ B.t0 N N' L L' hA) M ρ hD hcoef (t0' ρ) (ht0' ρ)).1, genus_one_norm_sq_eq]
  have key : meanLogNormSq D (tor0 D cc δ) L L' M (B.eNat χ N N' L L') =
      ((fF D * N * N' : ℕ) : ℝ) * ((∑ ρ : M →ₐ[ℚ] ℂ, Real.log (GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (G ρ))) /
        (Module.finrank ℚ M : ℝ)) := by
    unfold meanLogNormSq
    simp_rw [hnorm, Real.log_pow]
    rw [← Finset.mul_sum, mul_div_assoc]
  rw [key]
  have hv := sqrtDGammaLeLogV D
  unfold SqrtDGammaLeLogV at hv
  have hv0 : 0 ≤ Real.log D.host.v := Real.log_nonneg (one_le_v D)
  have hk : (0 : ℝ) ≤ ((fF D * N * N' : ℕ) : ℝ) := by positivity
  have habs := le_abs_self (logDerivativeAtOne D)
  have habs0 := abs_nonneg (logDerivativeAtOne D)
  have hLsc : 0 ≤ Lsc := by linarith
  have hb : (1 / 2) * (Real.log (Real.sqrt D.host.d) - Real.eulerMascheroniConstant + logDerivativeAtOne D) ≤ C * Lsc := by
    have h1 : (1 / 2) * (Real.log (Real.sqrt D.host.d) - Real.eulerMascheroniConstant + logDerivativeAtOne D) ≤ (1 / 2) * Lsc := by
      linarith
    have h2 : (1 / 2) * Lsc ≤ C * Lsc := mul_le_mul_of_nonneg_right hC hLsc
    linarith
  calc ((fF D * N * N' : ℕ) : ℝ) * ((∑ ρ : M →ₐ[ℚ] ℂ, Real.log (GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (G ρ))) /
        (Module.finrank ℚ M : ℝ))
      ≤ ((fF D * N * N' : ℕ) : ℝ) * ((1 / 2) * (Real.log (Real.sqrt D.host.d) - Real.eulerMascheroniConstant + logDerivativeAtOne D)) :=
        mul_le_mul_of_nonneg_left hmean hk
    _ ≤ ((fF D * N * N' : ℕ) : ℝ) * (C * Lsc) := mul_le_mul_of_nonneg_left hb hk
    _ = C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc := by push_cast; ring

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

end
