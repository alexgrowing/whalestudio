import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLinearForm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MapMemISupIsLinAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FVContinuousInvariantStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.ThetaTri in
theorem mem_omI_of_theta_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (φ v)) → φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ := by
  intro _ hP hL D P X A i j hj Y hc hμ φ hφ
  have hm := X.given.core.models
  have hθ : IsInfFam X.R.θ := hm.inf
  have hω := X.given.core.thP.ωP j (X.tupT (D.nd.mu i))
  have hp : (Vc D j).IsPosDef := hm.vpos j
  have hpd : ∀ τ, (gramAt D (Vc D j) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((j : ℕ) + 1)) τ
  have hHV := (hm.νV j (X.tupT (D.nd.mu i))).1.1
  have hfdV := (hm.νV j (X.tupT (D.nd.mu i))).2
  have hHW : (X.R.νW j).IsHaarMeasure := (hm.νW j).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D j)) (X.R.fdW j) (X.R.νW j) := (hm.νW j).2
  intro p
  have hφ' : ∀ v, IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ v) :=
    fun v => hω.om_pres _ _ (hφ v)
  refine ⟨hφ', fun F g => ?_, fun F y => ?_⟩
  · obtain ⟨hc1, hc2⟩ := _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant hL D P X A i j hj hμ F
    exact GlobalTheory.DefiniteQuotient.integrableOn_theta D X.R.ψ hω.std (Vc D j) (Wc D j) _ _ _ hω hpd _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2 _ _ hHV hfdV g
  · obtain ⟨hc1, hc2⟩ := _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant hL D P X A i j hj hμ F
    have hmap := (Classical.choose_spec (Classical.choose_spec hc)).2.2.1
    have hey : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) ∈ Formalism.IndefR.principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) := by
      rw [← hmap]; exact ⟨y, y.2, rfl⟩
    have hyv : _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y = _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) (fun τ => ((Classical.epsilon fun u : ↥(lowT (X.R.MW j (sg0 D X.A)) τ) =>
        ‖((u : (X.R.MW j (sg0 D X.A)).sm τ) : (X.R.MW j (sg0 D X.A)).H τ)‖ = 1 : ↥(lowT (X.R.MW j (sg0 D X.A)) τ)) :
          (X.R.MW j (sg0 D X.A)).sm τ)) := by
      simp [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap, kUnit, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
    obtain ⟨haut, hcu⟩ := GlobalTheory.T.multiplicitySpaceAllLevels_values_smooth_cuspidal X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) _ hey
      (fun τ => ((Classical.epsilon fun u : ↥(lowT (X.R.MW j (sg0 D X.A)) τ) =>
        ‖((u : (X.R.MW j (sg0 D X.A)).sm τ) : (X.R.MW j (sg0 D X.A)).H τ)‖ = 1 : ↥(lowT (X.R.MW j (sg0 D X.A)) τ)) :
          (X.R.MW j (sg0 D X.A)).sm τ))
    rw [← hyv] at haut hcu
    have hR := (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ haut hcu).conj
    have hgr := GlobalTheory.T.moderateGrowth_definiteThetaIntegral_vectorForm X.R.ψ (Vc D j) (Wc D j) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2
    have hct := GlobalTheory.T.continuous_definiteThetaIntegral_vectorForm X.R.ψ (Vc D j) (Wc D j) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2
    have hinv : ∀ γ ∈ GQ (Wc D j), ∀ g, (∫ h in X.R.fdV j (X.tupT (D.nd.mu i)),
        thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h (γ * g)
          (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h)) ∂(X.R.νV j (X.tupT (D.nd.mu i)))) =
        ∫ h in X.R.fdV j (X.tupT (D.nd.mu i)), thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h g
          (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h)) ∂(X.R.νV j (X.tupT (D.nd.mu i))) := by
      intro γ hγ g
      congr 1
      funext h
      have e : ((h, γ * g) : GA D (Vc D j) × GA D (Wc D j)) = (1, γ) * (h, g) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hφ' _))
    have := hR.integrableOn_modGrowth_mul hHW hfdW hgr hinv hct.aestronglyMeasurable
    convert this using 1
    funext g
    simp only [Pi.mul_apply, thIn]
    rw [mul_comm]
    rfl
end GlobalTheory.ThetaTri
end
end
