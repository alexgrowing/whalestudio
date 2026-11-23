import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedMeasureEqProdBesselRootMeasuresStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsQuotientMeasureUnipotentStabilisersStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocalStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AmpLift.amp_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf), s.relevant → s.G ≠ 0 → s.toTerm.atPt x.1 → Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 → IsFundR s x.2.2 → (∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v), ∀ y, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((s.pt.1 v)⁻¹ * (r * y))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((s.pt.1 v)⁻¹ * y))) → ∃ μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) ∧ (∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) ∧ hsNormSq (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * (x.2.1 x.2.2).toReal ^ 2 * ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (s.pt.1 v)) := by
  intro D X Y θ C u u' s x hrel _hG _hat hpin hfund hinv
  obtain ⟨μl, hμeq, hHaar, hHR, hroot⟩ := GlobalTheory.T.normalisedMeasure_eq_prod_besselRootMeasures D X Y θ C u u' s x.1 x.2.1 hpin
  obtain ⟨hq, ν, hν⟩ := GlobalTheory.T.exists_quotient_measure_unipotent_stabilisers D X u u' s.pt.1 μl hHaar
  choose νl hνl using hq
  refine ⟨μl, νl, hHaar, hνl, hroot, ?_⟩
  have hν' : IsQuotMeasS X.B.I x.2.1 ν := hμeq ▸ hν
  have hOO := Formalism.L2.SG.Pf.formAllC_holds D X Y u u' s x.2.1 ν x.2.2
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' s hrel) hHR hν' hfund.1 hfund.2
  have hprod := GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local D X u u' s.pt.1 μl νl ν hHaar hνl hν hinv
  unfold Formalism.L2.SG.TermOp.ampN
  rw [Formalism.L2.SG.LoopTerm.hsNormSq_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hOO,
    ← Complex.coe_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hprod]
  have hc : Complex.normSq (Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s.lam') : X.B.I.Gf) s.pt)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_pow]
  rw [hc, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring
