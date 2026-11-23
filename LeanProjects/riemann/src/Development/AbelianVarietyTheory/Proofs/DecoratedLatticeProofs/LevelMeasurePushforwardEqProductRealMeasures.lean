import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasLevW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFrameMemUH
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsRest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RealBoxMeasure

variable {D : D7}

theorem exists_realPart (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (hW : W.SigOK) (Fr : Frames W)
    (hFr : IsFrames W Fr) :
    ∃ φ : GA D W → ∀ ρ, Upq W ρ, Continuous φ ∧
      ∀ h ρ, UpqT.mat (φ h ρ) * Fr ρ = Fr ρ * infMat D.sp.cm.sig W.gram (θ ρ) h := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig W.rank W.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (W.sig (tauE D ρ)).1) (fun ρ => (W.sig (tauE D ρ)).2) Fr hcm hτ hθ (fun i => hW (tauE D i)) hFr
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig W.rank W.gram
  refine ⟨fun h => e1 (e0 h).1, e1.continuous.comp (continuous_fst.comp e0.continuous), fun h i => ?_⟩
  show UpqT.mat (e1 (e0 h).1 i) * Fr i = _
  rw [he1, (he0 h).2]; rfl

theorem mat_cancel (W : HSp D) (hW : W.SigOK) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau)
    {b b' : Upq W ρ} (h : UpqT.mat b * Fr ρ = UpqT.mat b' * Fr ρ) : b = b' := by
  obtain ⟨C, h1, -⟩ := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D ρ))).2.2 (Fr ρ) (hFr ρ)
  apply (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.2.injective
  have h5 := congrArg (· * C) h
  simpa only [Matrix.mul_assoc, h1, Matrix.mul_one] using h5

theorem realMat_of (W : HSp D) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau) (b : Upq W ρ)
    (M : Matrix (Fin W.rank) (Fin W.rank) ℂ) (h : UpqT.mat b * Fr ρ = Fr ρ * M) : realMat W Fr ρ b = M := by
  have hG := GlobalTheory.SmoothForms.RealPts.gramAt_unit W ρ
  unfold realMat conjFrame
  have e : (Fr ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * (Fr ρ * M) = gramAt D W ρ * M := by
    rw [← Matrix.mul_assoc, hFr ρ]
  rw [Matrix.mul_assoc (_ * _), h, e, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]

theorem realMat_mem (W : HSp D) (hW : W.SigOK) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau) (b : Upq W ρ) :
    realMat W Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ) :=
  conjFrame_mem_UH _ _ _ (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D ρ))).1 _ _ (hFr ρ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_unit W ρ) b

theorem infMat_realElt (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig W.gram (θ ρ) (realElt θ W u) = u ρ := by
  rw [realElt, GlobalTheory.RealTransSm.infMat_list_prod hθ u hu ρ _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ))]

theorem realElt_mem (θ : InfFam D) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    realElt θ W u ∈ GinfC W := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact GlobalTheory.PointAtPlaceHom.atTau_mem W τ (u τ)

theorem finE_realElt (θ : InfFam D) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    finE W (realElt θ W u) = 1 := by
  rw [Lev.finE_eq, (MonoidHom.mem_ker).1 (realElt_mem θ W u), map_one]

theorem continuous_realElt (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (hW : W.SigOK) (Fr : Frames W)
    (hFr : IsFrames W Fr) :
    Continuous fun b : (∀ ρ, Upq W ρ) => realElt θ W fun ρ => realMat W Fr ρ (b ρ) := by
  haveI : IsTopologicalGroup (GA D W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  unfold realElt
  refine continuous_list_prod _ fun ρ _ => ?_
  have hκ : Continuous fun b : (∀ ρ, Upq W ρ) => realMat W Fr ρ (b ρ) := by
    unfold realMat conjFrame
    exact continuous_const.matrix_mul (((continuous_const.matrix_mul
      ((GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.2.continuous.comp (continuous_apply ρ))).matrix_mul continuous_const))
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ W ρ).comp_continuous hκ
    fun b => realMat_mem W hW Fr hFr ρ (b ρ)

theorem lintegral_levelSet_eq_pi : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ENNReal, Measurable Z → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → MeasurableSet {h : GA D W | finE W h ∈ K} → ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν = ∫⁻ b, Z (realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  intro D θ hθ W hW K ν hν Fr hFr mR hmR Z hZ hZK hS
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable W
  haveI := hsc
  haveI := hbo
  haveI : ∀ ρ, SigmaFinite (mR ρ) := fun ρ => by haveI := (hmR ρ).1; infer_instance
  obtain ⟨φ, hφc, hφ⟩ := exists_realPart θ hθ W hW Fr hFr
  have hφm : Measurable φ := hφc.measurable
  set sec : (∀ ρ, Upq W ρ) → GA D W := fun b => realElt θ W fun ρ => realMat W Fr ρ (b ρ) with hsec
  have hsecm : Measurable (fun b => Z (sec b)) := hZ.comp (continuous_realElt θ hθ W hW Fr hFr).measurable
  obtain ⟨-, -, H⟩ := hν
  obtain ⟨-, H1⟩ := H θ hθ
  obtain ⟨-, H2⟩ := H1 Fr hFr
  have hpi : Measure.pi mR = Measure.map φ (ν.restrict {h : GA D W | finE W h ∈ K}) := by
    refine Measure.pi_eq fun B hB => ?_
    have hm : MeasurableSet (φ ⁻¹' Set.univ.pi B) := hφm (MeasurableSet.univ_pi hB)
    rw [Measure.map_apply hφm (MeasurableSet.univ_pi hB), Measure.restrict_apply hm, ← H2 mR hmR B hB]
    congr 1
    ext h
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
    rw [and_comm]
    refine and_congr_right fun _ => forall_congr' fun ρ => ⟨fun hb => ⟨φ h ρ, hb, hφ h ρ⟩, ?_⟩
    rintro ⟨b, hb, hbe⟩
    rwa [mat_cancel W hW Fr hFr ρ (hbe.trans (hφ h ρ).symm)] at hb
  have hfac : ∀ h ∈ {h : GA D W | finE W h ∈ K}, Z h = Z (sec (φ h)) := by
    intro h hh
    have e : ∀ ρ, infMat D.sp.cm.sig W.gram (θ ρ) (sec (φ h)) = infMat D.sp.cm.sig W.gram (θ ρ) h := fun ρ => by
      rw [hsec]
      dsimp only
      rw [infMat_realElt θ hθ W _ (fun τ => realMat_mem W hW Fr hFr τ _) ρ]
      exact realMat_of W Fr hFr ρ _ _ (hφ h ρ)
    have hk : (sec (φ h))⁻¹ * h ∈ levA W K := by
      refine ⟨(GlobalTheory.SmoothForms.RealPts.glue θ hθ W).1 _ fun ρ => ?_, ?_⟩
      · rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e ρ, ← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel,
          GlobalTheory.PointAtPlaceHom.infMat_one]
      · show finE W ((sec (φ h))⁻¹ * h) ∈ K
        rw [map_mul, map_inv, hsec]
        dsimp only
        rw [finE_realElt, inv_one, one_mul]
        exact hh
    rw [← hZK (sec (φ h)) _ hk, mul_inv_cancel_left]
  calc ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν
      = ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z (sec (φ g)) ∂ν := setLIntegral_congr_fun hS hfac
    _ = ∫⁻ b, Z (sec b) ∂(Measure.map φ (ν.restrict {h : GA D W | finE W h ∈ K})) :=
        (lintegral_map hsecm hφm).symm
    _ = _ := by rw [← hpi]

end GlobalTheory.RealBoxMeasure
