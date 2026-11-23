import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk

theorem exists_doubled_weilDatum : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → ∃ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh := by
  intro H D ψ A B χA χB om h
  have h0 : ResEta D 1 0 := by
    have h1 := resEta_parity (m := 0) (resEta_mul h.resS (resEta_inv h.resS)) (by omega)
    rwa [show χA * χA⁻¹ = 1 from mul_inv_cancel χA] at h1
  have h2 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  exact H D ψ (dblSp A) B 1 χB h.1 h2 h.3 (resEta_parity h0 (by change 0 % 2 = (A.rank + A.rank) % 2; omega)) h.resT

end GlobalTheory.Core.Rk
