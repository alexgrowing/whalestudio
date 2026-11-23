import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem tprod_one_pol_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0 := by
  intro F _ _ P Q R S h
  let c : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ := (MvPolynomial.aeval (fun _ => (0:ℂ))).toLinearMap
  have key := congrArg (PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra ℂ (InfinitePlace F) ℂ).compLinearMap (fun _ => c))) h
  simp [PiTensorProduct.lift.tprod, c] at key

end GlobalTheory
