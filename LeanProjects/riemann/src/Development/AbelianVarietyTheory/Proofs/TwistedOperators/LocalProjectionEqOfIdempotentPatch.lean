import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizer
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompIdem

theorem projV_eq_of_idem : ∀ {D : D7} (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g k : GA D T) (ε : AE D), compFin D.host.F D.host.E v ε = 1 → Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → projV T v k = projV T v g := by
  intro D T v g k ε hε h
  apply GlobalTheory.AdelicU.matHom_injective _ D.sp.cm.sig T.gram
  apply Units.ext
  show (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (proj D.sp.cm.sig T.gram v k)).1 =
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (proj D.sp.cm.sig T.gram v g)).1
  rw [GlobalTheory.AdelicU.matHom_proj, GlobalTheory.AdelicU.matHom_proj]
  show ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram k).1).map (compFin D.host.F D.host.E v) =
    ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram g).1).map (compFin D.host.F D.host.E v)
  change (Formalism.L2.Theta.mt T k).map _ = (Formalism.L2.Theta.mt T g).map _
  rw [h, GlobalTheory.CompStab.map_idem, hε, sub_self, zero_smul, add_zero, one_smul]

end GlobalTheory.CompIdem
