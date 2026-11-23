import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNormAdelicSchwartzRationalTranslatesLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatDarbouxCoordsRationalMatrixIffRatPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRatPairFundamentalDomainAdelicIteratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalThetaSecondVariableDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainTsumRationalTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaSumRationalPairInvariantStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegelUnfold

open MeasureTheory

set_option maxHeartbeats 1000000 in

theorem diag_theta_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
            @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
            ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) =
                c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro D ψ hψ S T JA JB ξ hJA hJB κ _ co hrat ν 𝓕 hν μ hμ
  letI mV : MeasurableSpace (κ → AF D.host.F) := borel _
  haveI : BorelSpace (κ → AF D.host.F) := ⟨rfl⟩
  letI mVV : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  have hψc : IsCharAF D.host.F ψ := hψ.1
  obtain ⟨lam, 𝓖, hlam, h𝓖, -, htr⟩ := GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar D S T κ co.e (GlobalTheory.T.ratDarbouxCoords_rationalMatrix_iff_ratPair D S T κ co.e hrat) ν 𝓕 hν
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.RatVecDomain.exists_fundamentalDomain D.host.F κ μ hμ
  obtain ⟨c₁, hc₁, hiter⟩ := GlobalTheory.T.integral_ratPairFundamentalDomain_adelic_iterated D.host.F κ μ hμ lam hlam 𝓖 h𝓖 𝓕₁ h𝓕₁ htop
  have hpos : 0 < μ.real 𝓕₁ := ENNReal.toReal_pos h0 htop
  refine ⟨((c₁ * μ.real 𝓕₁ : ℝ) : ℂ), Complex.ofReal_ne_zero.mpr (mul_pos hc₁ hpos).ne', fun Φ hΦ => ?_⟩

  set G : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ := fun p =>
    GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) Φ) with hGdef
  have hdiag : ∀ w, GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ (GlobalTheory.DiagSiegel.diagMat w) =
      G (co.e w) := by
    intro w
    have h1 : (GlobalTheory.DblSchr.ddr co).e (GlobalTheory.DiagSiegel.diagMat w) =
        (Sum.elim (co.e w).1 (co.e w).1, Sum.elim (co.e w).2 (-(co.e w).2)) := by
      rw [GlobalTheory.DblSchr.ddr, GlobalTheory.DblSchr.reD_e]
      have h2 : (GlobalTheory.DiagSiegel.diagMat w).submatrix id finSumFinEquiv.symm.symm = Matrix.fromCols w w := by
        ext i j
        simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_apply_apply, id]
      rw [h2]
      rfl
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, h1, hGdef]

  obtain ⟨B, hB⟩ := GlobalTheory.T.tsum_norm_adelicSchwartz_rationalTranslates_le D.host.F (κ ⊕ κ) Φ hΦ
  have hsumΦ : ∀ z : κ ⊕ κ → AF D.host.F, Summable fun ξ : κ ⊕ κ → D.host.F =>
      ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + z)‖ := fun z => by
    have h1 := GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F z hΦ)
    exact h1
  have hGbd : ∃ B : ℝ, ∀ w, ‖G w‖ ≤ B := by
    refine ⟨B, fun w => ?_⟩
    have hn : ∀ ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ =
        ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ := by
      intro ξ
      simp only [GlobalTheory.WeilM.schr, norm_mul, hψc.2.1, one_mul]
    have hs : Summable fun ξ : κ ⊕ κ → D.host.F => ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := by
      simp_rw [hn]
      exact hsumΦ _
    calc ‖G w‖ ≤ ∑' ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
          (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' ξ : κ ⊕ κ → D.host.F, ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ :=
          tsum_congr hn
      _ ≤ B := hB _
  have hGm : Measurable G := by
    letI mW : MeasurableSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := borel _
    haveI : BorelSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := ⟨rfl⟩
    have hm := GlobalTheory.ThetaTransformMeas.main D.host.F ψ hψc (κ ⊕ κ) Φ hΦ
    have hc : Continuous fun p : (κ → AF D.host.F) × (κ → AF D.host.F) =>
        ((Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) : (κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := by
      refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_) <;> rcases i with i | i
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_snd
      · exact ((continuous_apply i).comp continuous_snd).neg
    exact hm.comp hc.measurable
  have hGper : ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, ∀ w, G (γ + w) = G w :=
    fun γ hγ w => GlobalTheory.T.diagonalThetaSum_rationalPair_invariant D.host.F ψ hψc κ Φ γ hγ w

  set h : (κ → AF D.host.F) → ℂ := fun u => Φ (Sum.elim u u) with hhdef
  have hcont : Continuous h :=
    (GlobalTheory.ThetaUnfold.schA_continuous D.host.F hΦ).comp
      (continuous_pi fun i => by rcases i with i | i <;> exact continuous_apply i)
  have hhbd : ∃ B : ℝ, ∀ x : κ → AF D.host.F, Summable (fun η : κ → D.host.F =>
      ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖) ∧
      ∑' η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ ≤ B := by
    refine ⟨B, fun x => ?_⟩
    have hj : Function.Injective fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F) := by
      intro η η' e
      funext i
      exact congrFun e (Sum.inl i)
    have key : ∀ η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ =
        ((fun ξ : κ ⊕ κ → D.host.F => ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim x x)‖) ∘
          fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F)) η := by
      intro η
      simp only [hhdef, Function.comp_apply]
      congr 2
      funext i
      rcases i with i | i <;> rfl
    simp_rw [key]
    exact ⟨(hsumΦ _).comp_injective hj,
      (tsum_comp_le_tsum_of_inj (hsumΦ _) (fun _ => norm_nonneg _) hj).trans (hB _)⟩
  have hinner : ∀ x, ∫ y in 𝓕₁, G (x, y) ∂μ = (μ.real 𝓕₁ : ℂ) *
      ∑' η : κ → D.host.F, h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x) := by
    intro x
    exact GlobalTheory.T.integral_diagonalTheta_secondVariable_diagonal D.host.F ψ hψc κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ x
  calc GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ)
      = ∫ w in 𝓕, G (co.e w) ∂ν := by
        unfold GlobalTheory.DiagSiegel.thetaDiagInt
        simp_rw [hdiag]
    _ = ∫ p in 𝓖, G p ∂lam := htr G
    _ = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := hiter G hGm hGper hGbd
    _ = c₁ * ((μ.real 𝓕₁ : ℂ) * ∫ u, h u ∂μ) := by
        simp_rw [hinner]
        rw [integral_const_mul, GlobalTheory.T.integral_fundamentalDomain_tsum_rationalTranslates D.host.F κ μ hμ 𝓕₁ h𝓕₁ htop h hcont hhbd]
    _ = ((c₁ * μ.real 𝓕₁ : ℝ) : ℂ) * GlobalTheory.DiagSiegel.diagInt μ Φ := by
        push_cast
        rw [mul_assoc]
        rfl

end GlobalTheory.DiagSiegelUnfold

end
