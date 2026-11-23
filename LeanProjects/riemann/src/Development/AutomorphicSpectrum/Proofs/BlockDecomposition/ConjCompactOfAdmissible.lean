import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs
open GroundTheory.Automorphic.Reduction (adelicBorel posIdele diagUnits coe_diagUnits)
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.SiegelConj

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]

def scal (s : ℝ) : Ad E := 1 - GlobalTheory.CuspRep.sInf E 1 + GlobalTheory.CuspRep.sInf E (fun _ => (s : ℂ))

variable {E}

variable {n : ℕ}

def cell (S : Set (GA E n)) (R : ℝ) : Set (Matrix (Fin n) (Fin n) (Ad E)) :=
  (fun q : GA E n × (Fin n → Fin n → ℝ) =>
    Matrix.of fun i j => (q.1 : Matrix (Fin n) (Fin n) (Ad E)) i j * scal E (q.2 i j)) ''
    (S ×ˢ Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc 0 R)

end GlobalTheory.CompanionTheory.SiegelConj

end
