import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointTermAndLiftSameRealDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalRealDataFunctionsEquivariantContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientMeasureBesselModelOfLocalQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RMeasExAll
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpLoc

theorem hsNormSq_amp_loc : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (τ : D.what₂.Tau) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → (∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) → hsNormSq ((locS hB u u' τ).J (nu1 hI C t τ) (gamR hI C t τ)) = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) * hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Formalism.L2.SG.RealObj.Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (s.pt.1 (vOf X τ))) := by
  intro D X Y hF hI C hB u u' t s hs hG hr hGap τ μ ν hμ hq hroot
  have hW : ∀ τ', GoodW D τ' u u' 1 (locW C u u' τ') := fun τ' =>
    goodW_of C u u' τ' (Formalism.L2.SG.Pf.colsTypeTr C u τ') (Formalism.L2.SG.Pf.colsTypeTr C u' τ')
      (Formalism.L2.SG.Pf.zTr C u τ') (Formalism.L2.SG.Pf.zTr C u' τ') (Formalism.L2.SG.Pf.haarTr C τ')
  have e1 := Formalism.L2.SG.Pf.LocJEq.locJ_map_eq' C hB u u' τ (s.pt.1 (vOf X τ)) ν
  have hR2 : RMeas D (locW C u u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) 1
      (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ)))) := by
    obtain ⟨p, hp⟩ := hroot
    refine ⟨p, _, hp, ?_⟩
    rw [ENNReal.ofReal_one, one_smul]
    exact GlobalTheory.T.quotientMeasure_besselModel_of_local_quotient D X 1 C τ (s.pt.1 (vOf X τ)) μ ν hμ hq
  obtain ⟨a, ha, a', ha', hga⟩ := GlobalTheory.T.real_point_term_and_lift_same_real_double_coset D X Y hF hI 1 C u u' t s hs τ
  have hR4 : RMeas D (locW C u u' τ) (gamR hI C t τ) 1 (nu1 hI C t τ) := by
    have h := GlobalTheory.RMeasAll.rMeasEx_all D X Y hF hI C u u' hW t hG hr τ
    unfold nu1
    rw [dif_pos h]
    exact h.choose_spec
  obtain ⟨p0, hp0⟩ := relPtEx_holds hI C u u' t hG hr τ
  obtain ⟨hΦ, hΦ', hc, hc'⟩ := GlobalTheory.T.localRealData_functions_equivariant_continuous D X 1 C hB u u' τ hGap
  have h5 := GlobalTheory.T.hsNormSq_amplitude_doubleCoset_invariant D τ u u' 1 (locW C u u' τ) (locS hB u u' τ) (hW τ)
    (Nat.cast_pos.2 (D.mem u).A.T_prime.pos) (Nat.cast_pos.2 (D.mem u').A.T_prime.pos) hΦ hΦ' hc hc'
    (gamR hI C t τ) a a' p0 (nu1 hI C t τ) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ))))
    hp0 ha ha' hR4 (by rw [← hga]; exact hR2)
  rw [← h5, ← hga, e1]
  exact Formalism.L2.SG.LoopTerm.hsNormSq_smul _ _

end GlobalTheory.AmpLoc
