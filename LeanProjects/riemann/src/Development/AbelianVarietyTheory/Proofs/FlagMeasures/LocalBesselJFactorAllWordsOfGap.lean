import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LiftOntoCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantLiftNormalisedDataExistStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeConstantEqProdCovolumesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UMatMulLoc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermHasRealRelativePointStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedLiftAmplitudeEqCovolumeMulLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeWittLiftEqQuotientIntegralStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JFactTie

theorem jFactN_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  intro D X Y hF hI C hB u u' hGap t hG hr
  have hex : ∃ s : TT Y u u', s.toTerm = tc hI t :=
    Formalism.L2.SG.Pf.liftOntoC_of Formalism.L2.SG.Pf.WittFlags.LatIso_holds D X Y u u' (tc hI t)
  have hs : hex.choose.toTerm = tc hI t := hex.choose_spec
  have hrel : hex.choose.relevant := by
    show hex.choose.toTerm.relevant
    rw [hs]
    exact (hI.relevant t).1 hr
  have hsG : hex.choose.G ≠ 0 := by
    show hex.choose.toTerm.G ≠ 0
    rw [hs]
    intro h0
    apply hG
    apply (algebraMap D.host.F D.host.E).injective
    rw [gterm_val hI t, h0, map_zero]
  have hP : HasPin hex.choose := GlobalTheory.T.relevantLift_normalisedData_exist D X Y u u' hex.choose hrel hsG
  have hx := hP.choose_spec
  have hJ : JtOf hI t = Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') hex.choose := by
    unfold JtOf; rw [dif_pos hex]
  have hV : volRC hI t = (hP.choose.2.1 hP.choose.2.2).toReal := by
    unfold volRC covR; rw [dif_pos ⟨hr, hG, hex⟩, dif_pos hP]
  have hinv : ∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (hex.choose.pt.1 v), ∀ y,
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * (r * y))) =
        Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * y)) := by
    intro v
    obtain ⟨τ, rfl⟩ : ∃ τ, v = vOf X τ := ⟨X.pl v, by simp [vOf]⟩
    obtain ⟨p, hp⟩ := GlobalTheory.T.relevant_term_has_real_relative_point D X Y hF hI 1 C u u' t hex.choose hs hG hr τ
    exact GlobalTheory.StabInv.stab_inv D X 1 C hB u u' τ (hex.choose.pt.1 (vOf X τ)) p hGap hp
  obtain ⟨μl, νl, hH, hQ, hR, hA⟩ := GlobalTheory.T.normalisedLift_amplitude_eq_covolume_mul_local D X Y 1 C u u' hex.choose hP.choose hrel hsG hx.1 hx.2.1 hx.2.2 hinv
  have hloc : ∀ τ, j1 hI C hB t τ = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) *
      hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ))) := by
    intro τ
    haveI : SigmaFinite (μl (vOf X τ)) := (hH (vOf X τ)).1
    exact GlobalTheory.T.localAmplitude_wittLift_eq_quotientIntegral D X Y hF hI C hB u u' t hex.choose hs hG hr hGap τ (μl (vOf X τ)) (νl (vOf X τ)) inferInstance
      (hQ (vOf X τ)) (hR τ)
  have hK := GlobalTheory.T.amplitudeConstant_eq_prod_covolumes D X Y hF 1 C hB u u' one_pos hGap
  have hre : (∏ τ, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ)))) =
      ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (hex.choose.pt.1 v)) :=
    Fintype.prod_equiv X.pl.symm _ _ (fun τ => rfl)
  have hcov : covN (Y := Y) C u * covN (Y := Y) C u' =
      ((Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := rfl
  rw [hJ, hV, hA, hcov]
  unfold P1
  rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, hre, hK]
  ring

end GlobalTheory.JFactTie
