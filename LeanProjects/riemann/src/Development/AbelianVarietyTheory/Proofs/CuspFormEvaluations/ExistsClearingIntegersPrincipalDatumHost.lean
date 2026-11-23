import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastMemDifferentIdealPowLeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.HostClear

theorem absNorm_pos (D : D7) : 0 < Ideal.absNorm D.host.ccK :=
  Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem d_pos (D : D7) : 0 < D.host.d := D.host.hyp.2.1.pos

theorem sqrt_ne_zero (D : D7) : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have h1 := D.host.sqrtMinusD_sq
  rw [h] at h1
  have h2 : (D.host.d : D.host.E) = 0 := by linear_combination h1
  exact (d_pos D).ne' (by exact_mod_cast h2)

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) :
    ‖τ D.host.xi0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
  have hn : ‖τ D.host.sqrtMinusD‖ ^ 2 = D.host.d := by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg, Complex.norm_natCast]
  have h1 : ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  unfold Formalism.BasicNotions.Host.xi0
  rw [map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, h1]

theorem different_le (D : D7) : differentIdeal ℤ (𝓞 D.host.E) ≤ D.host.𝔟 := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)]
  refine (Ideal.mul_le_inf.trans inf_le_left).trans ?_
  rw [D.host.𝔟_spec.1]
  exact Ideal.mul_le_inf.trans inf_le_left

theorem isIntegral_mul_of_mem (D : D7) {z : 𝓞 D.host.E} (hz : z ∈ D.host.𝔟) {a : D.host.E} (ha : a ∈ D.host.AA) :
    IsIntegral ℤ ((z : D.host.E) * a) := by
  obtain ⟨hB, -⟩ := bB_ne D
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at ha
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB] at ha
  obtain ⟨w, -, hw⟩ := (FractionalIdeal.mem_coeIdeal _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  have : (z : D.host.E) * a = (w : D.host.E) := by
    rw [mul_comm]; exact hw.symm
  rw [this]
  exact w.isIntegral_coe

theorem absNorm_mem_AA (D : D7) : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA := by
  obtain ⟨hB, -⟩ := bB_ne D
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB]
  intro y hy
  obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    rwa [map_natCast] at this
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, D.host.ccE.mul_mem_right z h1, ?_⟩
  rw [map_mul, map_natCast]

theorem host_clear : ∀ (D : D7) (L : ℝ), 2 ≤ L → lrd D ≤ 2 * L → Real.log D.host.d ≤ 2 * L → Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * L → (∃ NA : ℕ, 0 < NA ∧ (∀ a ∈ D.host.AA, IsIntegral ℤ ((NA : D.host.E) * a)) ∧ Real.log NA ≤ 4 * L) ∧ ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA ∧ 0 < Ideal.absNorm D.host.ccK ∧ (∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : D.host.E) * (2 * D.host.xi0)) ∧ Real.log m ≤ 4 * L) ∧ Real.log (1 / (2 * xiR D)) ≤ 3 * L ∧ fdeg D.host.E = D.R.f ∧ Real.log (dE D.host.E) ≤ 4 * fdeg D.host.E * L ∧ Real.log (rdE D.host.E) ≤ 2 * L ∧ D.R.f ≤ D.R.r ∧ 1 ≤ D.R.f ∧ ReciprocityTheory.ChartRestriction.G.FD.cc D.host.xi0 = -D.host.xi0 ∧ D.host.xi0 ≠ 0 ∧ (∀ τ : D.host.E →+* ℂ, ‖τ D.host.xi0‖ = xiR D) := by
  intro D L hL hrd hd hc
  have hN := absNorm_pos D
  have hd0 := d_pos D
  have hNR : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
  have hdR : (0 : ℝ) < D.host.d := by exact_mod_cast hd0
  have hNE : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hs := sqrt_ne_zero D
  have hfin := GlobalTheory.PinNum.finrank_host D
  have hf1 : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    unfold Ranks.f; omega
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hfd : fdeg D.host.E = D.R.f := by
    unfold fdeg; rw [hfin]; omega
  have hdisc : 0 < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hlog : Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| ≤ 4 * D.R.f * L := by
    unfold lrd at hrd
    rw [div_le_iff₀ (by positivity)] at hrd
    linarith
  refine ⟨?_, absNorm_mem_AA D, hN, ?_, ?_, hfd, ?_, ?_, ?_, hf1, conj_xi0_alt D, ?_, ?_⟩
  · have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    obtain ⟨N, hN0, hNm, hNle⟩ := GlobalTheory.T.exists_natCast_mem_differentIdeal_pow_le_discr_sq D.host.E
    refine ⟨N, hN0, fun a ha => ?_, ?_⟩
    · have := isIntegral_mul_of_mem D (different_le D hNm) ha
      simpa using this
    · have hNR' : (0 : ℝ) < N := by exact_mod_cast hN0
      have h1 := Real.log_le_log (by positivity) hNle
      rw [Real.log_pow, Real.log_pow, hfin] at h1
      push_cast at h1
      have h2 : (D.R.f : ℝ) * Real.log N ≤ D.R.f * (4 * L) := by linarith
      exact le_of_mul_le_mul_left h2 (by linarith)
  · refine ⟨Ideal.absNorm D.host.ccK * D.host.d, Nat.mul_pos hN hd0, ?_, ?_⟩
    · have h1 : ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : D.host.E) * (2 * D.host.xi0) =
          2 * D.host.sqrtMinusD := by
        have h2 : (D.host.d : D.host.E) = -D.host.sqrtMinusD ^ 2 := by
          rw [D.host.sqrtMinusD_sq, neg_neg]
        unfold Formalism.BasicNotions.Host.xi0
        push_cast
        rw [h2]
        field_simp
      rw [h1]
      exact IsIntegral.mul (by exact_mod_cast isIntegral_natCast (R := ℤ) (B := D.host.E) 2) (sqrtMinusD_isIntegral D)
    · push_cast
      rw [Real.log_mul hNR.ne' hdR.ne']
      linarith
  · have hsq : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 hdR
    have h1 : 1 / (2 * xiR D) = (Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d / 2 := by
      unfold xiR
      rw [norm_embedding_hostFormConstant_eq]
      field_simp
    rw [h1, Real.log_div (by positivity) two_ne_zero, Real.log_mul hNR.ne' hsq.ne', Real.log_sqrt hdR.le]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  · rw [hfd]; exact hlog
  · unfold rdE dE
    rw [Real.log_rpow hdisc, hfin]
    unfold lrd at hrd
    push_cast
    rw [one_div_mul_eq_div]
    exact hrd
  · have h1 := D.R.f_le_k
    have h2 := D.R.two_le_m
    unfold Ranks.f Ranks.n Ranks.r
    omega
  · unfold Formalism.BasicNotions.Host.xi0
    exact div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero hNE hs)
  · intro τ
    unfold xiR
    rw [norm_embedding_hostFormConstant_eq, norm_embedding_hostFormConstant_eq]

end GlobalTheory.HostClear
