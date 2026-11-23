import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLinearCombinationIsTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetValueTangentCombinationSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedFibreLieBasisLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedModelSectionNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFiltrationSectionCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedFibreRigidModelJetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidModelSectionJetEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionIndexCoveringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexEmbeddingSectionPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedFibreHermitianRigidDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRankBoundSetupStatement

namespace GlobalTheory.SecJetLem

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

theorem filt_le_of_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V] (J J' : ℕ → V →ₗ[K] K) (a : K)
    (hJ : ∀ k, J' k = a ^ k • J k) : ∀ i, filt J i ≤ filt J' i
  | 0 => le_rfl
  | i + 1 => by
    refine inf_le_inf (filt_le_of_smul J J' a hJ i) fun v hv => ?_
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hJ, LinearMap.smul_apply, hv, smul_zero]

end GlobalTheory.SecJetLem

namespace GlobalTheory.SecJetLem

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

theorem secJets4 : Hypotheses2 → GlobalTheory.Published.MoretBaillyModel → GlobalTheory.LieHt.SecJets4 := by
  intro hP hMB K _ _ F h ρ hh hρ K' _ _ _ x hx n hn
  obtain ⟨K'', _, _, _, _, _, P, ψ, AA, _, _, φ, MM, w, b, E, hE, hPF, hM, hbij, hEiff, hL2, hfull, hmu, hdeg⟩ :=
    hMB K F h hh (4 * n) (by omega) K'
  obtain ⟨h'', hbc⟩ := (GlobalTheory.T.hermitian_lattice_base_change K K'' F.P₀.g h F.lieLat (GlobalTheory.T.semi_fibration_lie_lattice_full K F).1.1).1
  obtain ⟨v', hv', hbasis⟩ := GlobalTheory.T.polarized_fibre_lie_basis_lift K F K'' P ψ hPF
  obtain ⟨i₀, hi₀⟩ := GlobalTheory.T.exists_section_index_covering K'' P (4 * n)
  set x'' : Fin F.P₀.g → K'' := fun i => algebraMap K' K'' (x i) with hx''def
  have hx'' : x'' ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa [x''] using this
  set J := jetFun (tanComb x'' v') i₀ (rigVal w i₀) b with hJdef
  refine ⟨K'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h'', hbc,
    (4 * n) ^ F.P₀.g, hE, E, filt J, J, hfull, hmu, hdeg, rfl, fun i hi => ⟨rfl, ?_, ?_, ?_⟩⟩
  · exact GlobalTheory.T.jet_filtration_section_combination K'' P F.P₀.g v' x'' n _ b i₀ (rigVal w i₀) hbasis hx'' (by omega) hbij hi₀
      (GlobalTheory.T.rigidified_model_section_nonvanishing K'' P AA φ MM (4 * n) w i₀ hM hi₀) i hi
  · intro v hvE hvF a ha
    obtain ⟨t, ht⟩ := (hEiff v).1 hvE
    obtain ⟨Y, hYt, hYv⟩ := GlobalTheory.T.polarized_fibre_rigid_model_jets K F K'' P ψ AA φ MM (4 * n) w v' hP hPF hM hv' (a • x'') ha
    have hJa : ∀ k, jetFun (tanComb (a • x'') v') i₀ (rigVal w i₀) b k = a ^ k • J k := by
      intro k
      refine LinearMap.ext fun c => ?_
      rw [jetFun_apply, LinearMap.smul_apply, hJdef, jetFun_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [GlobalTheory.T.jet_value_tangent_combination_smul]
      ring
    have := GlobalTheory.T.rigid_model_section_jet_evaluation K'' P AA φ MM (4 * n) w _ b i₀ (tanComb (a • x'') v') Y v t i hM hi₀ hYt hYv ht
      (filt_le_of_smul J _ a hJa i hvF)
    rwa [hJa, LinearMap.smul_apply, smul_eq_mul] at this
  · intro σ q vv cc hvv
    obtain ⟨Q, ψσ, wσ, s, u, Hm, χ, ρ', θ, Fd, yq, Y0, Ef, hPFσ, hwσ, hs, hAH, hRig, hFn, hTh, hFd, hyq, hY0, hnrm,
      hleast, hEf, hEfb, hρ'⟩ :=
      GlobalTheory.T.polarized_fibre_hermitian_rigid_data K F h ρ K'' h'' P ψ AA φ MM (4 * n) w _ b v' x'' σ (by omega) hh hρ hbc hPF hM hv' hbasis
    have hform := fun a b' => hL2 σ Q ψσ wσ s u Hm χ ρ' θ Fd hPFσ hwσ hs hAH hRig hFn hFd a b'
    have hcmp : ∀ c ∈ filt J i, σ (J i c) * ρ' =
        iteratedDeriv i (fun t : ℂ => ∑ a, σ (c a) * θ a (t • Y0)) 0 := fun c hc =>
      GlobalTheory.T.complex_embedding_section_pullback K'' P AA φ MM (4 * n) w _ b i₀ (tanComb x'' v') σ Q ψσ wσ s F.P₀.g u ρ' θ yq Y0 c i hM hi₀
        (GlobalTheory.T.tangent_linear_combination_isTangent K'' P.A F.P₀.g v' x'' fun k => hbasis.1 k) hPFσ hwσ hs hRig hFn hyq hY0 hc
    have := GlobalTheory.T.theta_function_rank_bound_setup K'' σ F.P₀.g _ hE Q.A Q.L u Hm χ Ef (4 * n) i θ Fd ρ' (ρ (σ.comp (algebraMap K K''))) Y0 (J i)
      (filt J i) (by omega) hAH hTh hFd hEf hEfb hleast hform hcmp hρ' q vv cc hvv
    rw [hnrm]
    exact this

end GlobalTheory.SecJetLem
