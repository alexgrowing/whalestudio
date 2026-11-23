import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSumFockHeisenbergISmulSignConjVacuum

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD

namespace GlobalTheory.FockVacD

theorem sumPl_heisOp_vacuum_dep {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))
        (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))
        (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [GlobalTheory.FockVac.atPl_tprod, GlobalTheory.FockVac.atPl_tprod, GlobalTheory.FockVac.heisOp_one,
    MultilinearMap.map_update_smul]

end GlobalTheory.FockVacD
