import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenSubgroupFiniteSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.ThetaLevel

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  have h1 : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, z ^ i‖ := by
    intro N
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have : ∀ i ∈ Finset.range N, (1 / 2 : ℝ) ≤ (z ^ i).re := by
      intro i _
      have h2 := (Complex.abs_re_le_norm (z ^ i - 1)).trans_lt (h i)
      rw [Complex.sub_re, Complex.one_re, abs_lt] at h2
      linarith [h2.1]
    have h3 := Finset.sum_le_sum this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
    linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have h4 := h N
  rw [← geom_sum_mul, norm_mul] at h4
  rw [div_lt_iff₀ hpos] at hN
  nlinarith [h1 N]

theorem eventually_smul (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hw : GlobalTheory.Ker.IsWeak ψ S T om)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∃ c : ℂ, om p f = c • f := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  filter_upwards [GlobalTheory.T.eventually_weilMatrixCoeff_finitePoint_invariant D ψ hψ S T μ 𝓕 hμ h𝓕 f hf] with p hp h1 h2
  obtain ⟨g, h⟩ := p
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.thetaFunction_eq_unitSmul_of_diagonalCoefficient_eq D ψ hψ S T μ 𝓕 hμ h𝓕 f (om (g, h) f) hf (hw.om_pres _ f hf) (fun w => by
    have e : actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := GlobalTheory.AdelicLatMove.actO_actO_inv S T g h w
    have e1 := hp h1 h2 (actO S T g⁻¹ h⁻¹ w)
    have e2 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om (g, h)) (hw.om_pres _) (hw.om_unit μ 𝓕 hμ h𝓕 _)
      (heisO ψ S T (actO S T g⁻¹ h⁻¹ w) f) f (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hf
    rw [hw.om_heis g h _ f hf, e] at e2
    simp only [e] at e1
    exact e2.trans e1.symm)
  exact ⟨c, hc⟩

theorem exists_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ f, IsThetaFunO ψ S T f → ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧ IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → om (k, k') f = f := by
  intro D ψ hψ S T om hw hc f hf
  by_cases h0 : f = 0
  · exact ⟨⊤, ⊤, by simp, by simp, fun k _ _ k' _ _ => by rw [h0, map_zero]⟩
  obtain ⟨w, hw0⟩ := Function.ne_iff.1 h0
  have hw0 : f w ≠ 0 := hw0
  have hcont : Continuous fun p : GA D S × GA D T => ‖om p f w / f w - 1‖ :=
    (((hc f hf w).div_const _).sub continuous_const).norm
  have hnear : ∀ᶠ p : GA D S × GA D T in 𝓝 1, ‖om p f w / f w - 1‖ < 1 / 2 := by
    refine hcont.continuousAt.eventually_lt continuousAt_const ?_
    simp [div_self hw0]
  have hN := (eventually_smul D ψ hψ S T om hw f hf).and hnear
  obtain ⟨N, hN1, N', hN2, hsub⟩ := mem_nhds_prod_iff.1 (show _ ∈ 𝓝 ((1 : GA D S), (1 : GA D T)) from hN)
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D S N hN1
  obtain ⟨U', hU', hUN'⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D T N' hN2
  refine ⟨U, U', hU, hU', fun k hk hkf k' hk' hkf' => ?_⟩
  obtain ⟨c, hcf⟩ := (hsub (Set.mk_mem_prod (hUN k hk hkf) (hUN' k' hk' hkf'))).1 hkf hkf'
  have hpow : ∀ n : ℕ, om ((k, k') ^ n) f = c ^ n • f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hcf, map_smul, ih, smul_smul, pow_succ']
  have hc1 : c = 1 := eq_one_of_pow_near fun n => by
    have h := (hsub (Set.mk_mem_prod (hUN _ (pow_mem hk n) (pow_mem hkf n))
      (hUN' _ (pow_mem hk' n) (pow_mem hkf' n)))).2
    have e : om (k ^ n, k' ^ n) f = c ^ n • f := hpow n
    rw [e, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hw0] at h
    exact h
  rw [hcf, hc1, one_smul]

end GlobalTheory.Mem.ThetaLevel
