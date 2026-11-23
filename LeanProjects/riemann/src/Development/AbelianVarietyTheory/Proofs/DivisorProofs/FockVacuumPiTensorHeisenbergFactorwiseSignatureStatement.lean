import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumPiTensorHeisenbergFactorwiseSignature
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vacuum_pi_tensor_heisenberg_factorwise_signature : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ} (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
    sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  first | exact @GlobalTheory.FockVacD.sumPl_heisOp_vacuum_dep | exact GlobalTheory.FockVacD.sumPl_heisOp_vacuum_dep | (intros; apply GlobalTheory.FockVacD.sumPl_heisOp_vacuum_dep <;> assumption)
