import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelLeviDetHomLeviMulUnipotentStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw
namespace GlobalTheory.Core.Rk.SWLaw
variable {D : D7}

theorem scalar_eq (A B : HSp D) (χB : (AE D)ˣ →* Circle) (a : GL (Fin A.rank) (AE D)) :
    (((χB (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod B.rank a : ℝ) : ℂ) =
      ((χB⁻¹ (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (sZero A B + (A.rank : ℂ) / 2) := by
  rw [MonoidHom.inv_apply, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, npow, sZero, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  congr 2
  push_cast
  ring

theorem siegel_decomp (A : HSp D) (p : siegel A) :
    ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c :=
  GlobalTheory.T.doublingSiegel_eq_levi_mul_unipotent D A p

theorem aP_decomp (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank)
    (h : (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c) : aP A p = Matrix.GeneralLinearGroup.det a :=
  GlobalTheory.T.doublingSiegelLeviDetHom_levi_mul_unipotent D A p a c h

theorem zero_datum (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
    (omh : WRep (dblSp A) B) (hW : IsWeilDatumO ψ (dblSp A) B 1 χB omh) (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) :
    ∃ om₀ : GA D (zeroSp D) × GA D B →* Module.End ℂ (WO (zeroSp D) B → ℂ), IsWeilDatumO ψ (zeroSp D) B 1 χB om₀ := by
  refine hP D ψ (zeroSp D) B 1 χB hW.std hW.hecS hW.hecT ?_ hW.resT
  exact ⟨hW.resS.1, fun η _ a => by rw [show (zeroSp D).rank = 0 from rfl, pow_zero]; rfl⟩

theorem swSec_law : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ (p : siegel A) (g : GA D (dblSp A)), swSec A B omh ν 𝓕 φ (p * g) = (χB⁻¹ (aP A p) : Circle) * npow (absA D (aP A p)) (sZero A B + (A.rank : ℂ) / 2) * swSec A B omh ν 𝓕 φ g := by
  intro hP D ψ A B χB omh hW ν 𝓕 hν φ hφ p g
  obtain ⟨om₀, h₀⟩ := zero_datum ψ A B χB omh hW hP
  obtain ⟨a, c, hp⟩ := siegel_decomp A p
  have haP := aP_decomp A p a c hp
  have hν' : IsCovolOne (ratMx D B.rank A.rank) ν 𝓕 := hν
  have hF := hW.om_pres (g, 1) φ hφ
  set F := omh (g, 1) φ with hFdef
  have hF' := hW.om_pres ((dblDec A).nC c, 1) F hF
  have hM := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ (dblSp A) (zeroSp D) B A.rank (dblDec A) 1 χB omh om₀ hW h₀ ν 𝓕 hν'
  have h1 := (hM _ hF').levi a 0
  have h2 := (hM F hF).centre c 0
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec
  have e1 : omh (↑p * g, 1) φ = omh ((dblDec A).levi a, 1) (omh ((dblDec A).nC c, 1) F) := by
    rw [hp, hFdef, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    simp [Prod.mk_mul_mk, mul_assoc]
  rw [e1, ← mixS_dblDec_zero A B ψ ν 𝓕 _ 0, ← mixS_dblDec_zero A B ψ ν 𝓕 F 0, h1, Matrix.zero_mul, h2, map_zero, symplOH_zero_left, AddChar.map_zero_eq_one, one_smul, haP, Pi.smul_apply, smul_eq_mul]
  rw [scalar_eq A B χB a]

end GlobalTheory.Core.Rk.SWLaw

end
