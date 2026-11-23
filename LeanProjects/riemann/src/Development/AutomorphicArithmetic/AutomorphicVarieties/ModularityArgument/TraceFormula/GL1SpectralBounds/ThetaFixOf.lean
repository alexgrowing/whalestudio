import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MultiplicityOneRigidity.GelfandKazhdanDualOfRigidity
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PMultC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem theta_eq (g : GA E n) :
    GlobalTheory.ThetaPull.thetaA E n g = PhiU n (Ad E) * PositivityTheory.Rg.BcB.thetaA E n g * (PhiU n (Ad E))⁻¹ := by
  have e : GlobalTheory.ThetaPull.thetaA E n g = PhiU n (Ad E) * invT n (Ad E) (GeneralLinearGroup.map (conjAd E) g) *
      (PhiU n (Ad E))⁻¹ := rfl
  rw [e]
  congr 2

private theorem phi_rat : PhiU n (Ad E) = ratGL E n (PhiU n E) :=
  (GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU (algebraMap E (Ad E)) n).symm

private theorem phi_split : PhiU n (Ad E) = GlobalTheory.CsdFromConj.phiG E n := by
  refine ga_ext ?_ ?_
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CsdFromConj.toUnits_PhiK, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]

private theorem rt_phi_mem (π : CuspSub E n) {φ : Sm E n} (hφ : φ ∈ π.V) : rt E n (PhiU n (Ad E)) φ ∈ π.V := by
  have h := (GlobalTheory.CsdFromConj.phiEquiv π ⟨φ, hφ⟩).2
  rw [phi_split, GlobalTheory.CsdFromConj.rt_phiG]
  exact h

private theorem iso_theta {P : CuspSub E n} (h : P.IsCsd) : (GlobalTheory.ThetaPull.thetaSub P).Iso P := by
  obtain ⟨T, hT⟩ := h
  let L := (GlobalTheory.ThetaPull.pull E n).submoduleMap P.V
  refine ⟨L.symm.trans T, fun o φ => ?_⟩
  obtain ⟨φ, rfl⟩ := L.surjective φ
  have e : (GlobalTheory.ThetaPull.thetaSub P).op o (L φ) = L (P.op (thetaOp o) φ) :=
    Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1)
  rw [e]
  exact (congrArg T (L.symm_apply_apply _)).trans
    ((hT o φ).trans (congrArg (P.op o) (congrArg T (L.symm_apply_apply φ)).symm))

private theorem pull_mem {P : CuspSub E n} (h : P.IsCsd) {φ : Sm E n} (hφ : φ ∈ P.V) :
    GlobalTheory.ThetaPull.pull E n φ ∈ P.V := by
  have e : (GlobalTheory.ThetaPull.thetaSub P).V = P.V :=
    UpperTheory.V.Af.cuspMultOneGL E n _ _ (Quotient.sound (iso_theta h))
  rw [← e]
  exact ⟨φ, hφ, rfl⟩

theorem UpperTheory.V.Z.Tf.GOne.thetaFixOf :
    PositivityTheory.Rg.BcB.Desc.ThetaFixOf := by
  intro E _ _ _ n _ π hd
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired CuspFormAutomorphicBounds.automorphicFormsFiniteGL E n π
    (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n π) hd
  refine ⟨fun ψ hψ t g => GlobalTheory.BcSpehCompare.isNormalised_of_isCsd hc ψ hψ t g, fun ψ hψ => ?_⟩
  refine ⟨GlobalTheory.ThetaPull.pull E n (rt E n (PhiU n (Ad E)) ψ), pull_mem hc (rt_phi_mem π hψ), fun g => ?_⟩
  have e : PositivityTheory.Rg.BcB.thetaA E n g =
      ratGL E n (PhiU n E)⁻¹ * (GlobalTheory.ThetaPull.thetaA E n g * PhiU n (Ad E)) := by
    rw [theta_eq, map_inv, ← phi_rat]
    group
  rw [e, (π.cusp ψ hψ).1.left, GlobalTheory.ThetaPull.pull_apply, rt_apply]

end
