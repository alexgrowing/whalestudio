import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodularStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilBridge
open GlobalTheory.WeilSchrodinger

theorem det_ne_zero_of_nondeg (D : D7) {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E)
    (h : (sesq D G).Nondegenerate) : G.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  apply h.2 v
  intro x
  have e : ∀ i, ∑ j, G i j * v j = 0 := fun i => by
    have := congrFun hGv i
    simpa [Matrix.mulVec, dotProduct] using this
  simp only [sesq, Matrix.toLinearMapₛₗ₂'_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j _ => mul_comm (v j) (G i j), e i, mul_zero]

theorem exists_isTransport (D : D7) (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig)
    (S T : HSp D) (X : Spc D.host.F D.host.E T.rank) (Y : Spc D.host.F D.host.E S.rank) (r s r' s' : ℕ)
    (hX : X.IsHerm D.sp.cm.sig B r s) (hY : Y.IsSkew D.sp.cm.sig B r' s')
    (eA : X.J = T.gramᵀ)
    (eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Mo : Model D.sp.cm.sig X Y) (hMo : Mo.IsGood B.ψ) (χX χW : Chr D.host.F D.host.E)
    (hcX : GlobalTheory.LFun.IsHecke D.host.F D.host.E χX) (hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E χW)
    (rX : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX T.rank)
    (rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW S.rank)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig X Y) (hom : Mo.IsWeil B.ψ χX χW om) :
    ∃ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO B.ψ S T χW χX ω ∧ IsTransport B.ψ Mo.co ω om := by
  have hψ : IsStdChar D B.ψ (-1) := GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D B.ψ hB.std
  have rS := GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction D χW S.rank rW
  have rT := GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction D χX T.rank rX
  obtain ⟨ω, hω⟩ := GlobalTheory.weilRepresentationUnitaryPair D B.ψ S T χW χX hψ hcW hcX rS rT
  obtain ⟨om₀, hom₀⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB
    (Fin T.rank × Fin S.rank) Mo.co hMo.rat ω hω
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h6 := GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h7 := GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) B.ψ Mo.co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om₀ := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hw₀ : Mo.IsWeil B.ψ χX χW om₀ :=
    ⟨⟨isUSplitting_inr hsp, h6⟩, ⟨transD _ Mo.co, transD_e Mo.co, isUSplitting_inl hsp, h7⟩, h5⟩
  obtain ⟨h1X, h2X, -⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D B hB T.rank X r s hX
  obtain ⟨hdY, -⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D B hB S.rank Y r' s' hY
  have hdX : X.J.det ≠ 0 := by
    have := det_ne_zero_of_nondeg D X.Jᵀ h2X
    rwa [Matrix.det_transpose] at this
  have huniq := GlobalTheory.T.adelicWeilRep_schrodingerModel_unique D.host.F D.host.E D.sp.cm.sig hB.cm T.rank S.rank X Y Mo B.ψ χX χW hB.std hX.herm hdX
    hY.skew hdY.ne_zero om om₀ hom hw₀
  refine ⟨ω, hω, fun a b g h ha hb Φ hΦ => ?_⟩
  rw [huniq (a, b) Φ hΦ]
  exact hom₀ a b g h ha hb Φ hΦ

theorem thetaTr_zero (D : D7) {W : Type} [AddCommGroup W] [Module (AF D.host.F) W] {Bf : W → W → AF D.host.F}
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux Bf κ) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (κ → AF D.host.F) → ℂ) :
    thetaTr D.host.F d ψ Φ 0 = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  have : GlobalTheory.WeilM.schr ψ (0 : (κ → AF D.host.F) × (κ → AF D.host.F)) Φ = Φ := by
    funext x
    simp [GlobalTheory.WeilM.schr]
  simp [thetaTr, GlobalTheory.WeilM.Darboux.rho, this]

theorem exists_theta_eq (D : D7) (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig)
    (S T : HSp D) (X : Spc D.host.F D.host.E T.rank) (Y : Spc D.host.F D.host.E S.rank) (r s r' s' : ℕ)
    (hX : X.IsHerm D.sp.cm.sig B r s) (hY : Y.IsSkew D.sp.cm.sig B r' s')
    (eA : X.J = T.gramᵀ)
    (eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Mo : Model D.sp.cm.sig X Y) (hMo : Mo.IsGood B.ψ) (χX χW : Chr D.host.F D.host.E)
    (hcX : GlobalTheory.LFun.IsHecke D.host.F D.host.E χX) (hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E χW)
    (rX : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX T.rank)
    (rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW S.rank)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig X Y) (hom : Mo.IsWeil B.ψ χX χW om) :
    ∃ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO B.ψ S T χW χX ω ∧ IsTransport B.ψ Mo.co ω om ∧
      ∀ (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig X.J) (b : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Y.J) (g : GA D S) (h : GA D T),
        mt T h = a.1.1 → mt S g = (b⁻¹).1.1ᵀ → ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin T.rank × Fin S.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ a b = ω (g, h) (thetaTr D.host.F Mo.co B.ψ Φ) 0 := by
  obtain ⟨ω, hω, htr⟩ := exists_isTransport D B hB S T X Y r s r' s' hX hY eA eB Mo hMo χX χW hcX hcW rX rW om hom
  refine ⟨ω, hω, htr, fun a b g h ha hb Φ hΦ => ?_⟩
  rw [← (htr a b g h ha hb Φ hΦ).2, thetaTr_zero]
  rfl

end GlobalTheory.WeilBridge
