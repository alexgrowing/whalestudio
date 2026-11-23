import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFiberTypesAllStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTypeVecNonGalois
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GoodFirst
set_option maxHeartbeats 2000000 in
theorem firstTermCondition_forall_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → GoodFTAll (Dof x) := by
  intro hP hL
  have h := GlobalTheory.HeightCounting.Up.RowModel.overRows_allSt (_root_.GlobalTheory.T.nonGalois_typeVec_fixed_by_e0 hP)
  refine EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp fo tr w s P x l => ?_
  have hloc := H kp fo tr w s P x
  have ty : TypesTrue (Dof x).ntypes (Fr.at (w.st x.o.Z) f).P (Fr.at (w.st x.o.Z) f).W := x.fits.grp
  exact _root_.UpperTheory.Lit.Dz.firstTermCondition_all_stages hP.green hP.zel hL (Dof x) (cfOf x) (repOf x.r.Y) l.a
    (GlobalTheory.CoefDuty.OPinModel.labFixed_of_typesTrue ty) hloc
end GlobalTheory.GoodFirst
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allSt_goodFTAll_of_levelA : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → GoodFTAll (Dof x) := by
  first | exact @_root_.GlobalTheory.GoodFirst.firstTermCondition_forall_stages_alt | exact _root_.GlobalTheory.GoodFirst.firstTermCondition_forall_stages_alt | (intros; apply _root_.GlobalTheory.GoodFirst.firstTermCondition_forall_stages_alt <;> assumption)
end
end
