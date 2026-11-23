import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjugateWeilDatumHermitianSpaceNeg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_weilDatum_hermitianSpaceNeg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → (∀ f : WO A B → ℂ, IsThetaFunO ψ A B f → IsThetaFunO ψ (negSp A) B fun x => conj (f (-x))) ∧ ∃ om' : WRep (negSp A) B, IsWeilDatumO ψ (negSp A) B χA⁻¹ χB om' ∧ ∀ (g : GA D (negSp A)) (h : GA D B) (f : WO A B → ℂ), IsThetaFunO ψ A B f → om' (g, h) (fun x => conj (f (-x))) = fun x => (((χB (detA A (negEquiv A g)))⁻¹ : Circle) : ℂ) * conj (om (negEquiv A g, h) f (-x)) := by
  first | exact @GlobalTheory.NegWeil.exists_neg_datum | exact GlobalTheory.NegWeil.exists_neg_datum | (intros; apply GlobalTheory.NegWeil.exists_neg_datum <;> assumption)
