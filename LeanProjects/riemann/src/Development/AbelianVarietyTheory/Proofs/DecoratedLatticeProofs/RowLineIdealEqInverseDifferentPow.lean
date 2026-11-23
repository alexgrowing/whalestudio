import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeUnimodular
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.DiffInv

theorem aaD_eq_dI_pow : ∀ (D : D7) (i : Fin D.R.rS), aaD D i = dI D ^ (D.R.rS - i.1) := by
  intro D i
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  have hinv : dI D = (ddS D)⁻¹ := by
    rw [GlobalTheory.IntTerm.Conv.ddS_eq]
    exact eq_inv_of_mul_eq_one_left hP
  rw [hinv, inv_pow, aaD, ← Nat.cast_sub i.2.le, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.Core.Mi.LatMatch.DiffInv
