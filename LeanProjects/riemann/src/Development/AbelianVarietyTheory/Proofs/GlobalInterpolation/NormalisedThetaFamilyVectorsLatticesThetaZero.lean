import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.ProvisionExtensionLink
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqAndAlg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NatFamily

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf]

theorem exists_taylor_ne (D : D7) {N N' : ℕ} {F : VC D N N' → ℂ} (hF : Differentiable ℂ F) (h0 : F ≠ 0) :
    ∃ α, Formalism.MainNotions.TaylorLogMetric.taylor D F α ≠ 0 := by
  by_contra h
  push_neg at h
  apply h0
  funext z
  rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D hF z]
  simp [h]

theorem coef {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) {χ : IdE D → ℂ}
    (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : IsChi D χ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : admitted D N N' L L')
    (hmem : B.eNat χ N N' L L' ∈ Th D B.tor L L') :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D (B.eNat χ N N' L L') M := by
  have hC : Crv D cc δ := ⟨hcc, hδ⟩
  obtain ⟨χ', e, -, hv, -⟩ := GlobalTheory.TrueTheta.exists_family_of_curve D cc δ hC
  obtain ⟨he, hne, M₀, hfd, hM₀⟩ := hv N N' L L' hA
  obtain ⟨hN, hN', hL, hL'⟩ := hA
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N'
    (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)).1 _ hmem _ he hne
  have hdiff : Differentiable ℂ (e N N' L L') := he.1
  have htay : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α = c * Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := by
    intro α
    rw [hc]
    exact GlobalTheory.ProdThetaConj.taylor_const_mul hdiff c α
  obtain ⟨α₀, hα₀⟩ := exists_taylor_ne D hdiff hne
  have halg : Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α₀ ∈ Qbar := by
    have h := (GlobalTheory.MomEq.eq_and_alg).2 D cc δ B χ hcc hδ hχ N N' L L' ⟨hN, hN', hL, hL'⟩ 0
      ⟨1, one_pos, by simp⟩ α₀
    rwa [U_zero] at h
  have hM₀Q : ∀ x ∈ M₀, x ∈ Qbar := by
    intro x hx
    rw [mem_algebraicClosure_iff]
    have : IsIntegral ℚ (⟨x, hx⟩ : M₀) := IsIntegral.of_finite ℚ _
    exact (IntermediateField.isIntegral_iff.1 this).isAlgebraic
  have hcQ : c ∈ Qbar := by
    have e1 : c = Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α₀ / Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α₀ := by
      rw [htay, mul_div_cancel_right₀ _ hα₀]
    rw [e1]
    exact div_mem halg (hM₀Q _ (hM₀ α₀))
  have hcI : IsIntegral ℚ c := (mem_algebraicClosure_iff.1 hcQ).isIntegral
  haveI := IntermediateField.adjoin.finiteDimensional hcI
  refine ⟨M₀ ⊔ IntermediateField.adjoin ℚ {c}, inferInstance, fun α => ?_⟩
  rw [htay]
  exact mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {c} ≤ _) (IntermediateField.mem_adjoin_simple_self ℚ c))
    ((le_sup_left : M₀ ≤ _) (hM₀ α))

theorem family : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.VecP χ ∧ B.LatAll ∧ ∀ a b, B.ThZeroMem a b := by
  intro D cc δ B χ hcc hδ hχ
  have h0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.standard_basis_ok_link D cc hcc δ hδ B
  refine ⟨fun N N' L L' hA => ?_, B.latAll hcc hδ h0, fun a b => B.thZeroMem hS a b⟩
  have hv := B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA
  exact ⟨hv.1, hv.2, coef B hcc hδ hχ hA hv.1⟩

end GlobalTheory.NatFamily
