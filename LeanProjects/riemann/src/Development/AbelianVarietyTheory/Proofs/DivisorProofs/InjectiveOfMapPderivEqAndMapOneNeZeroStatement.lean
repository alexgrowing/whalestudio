import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfMapPderivEqAndMapOneNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_map_pderiv_eq_and_map_one_ne_zero : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V)
    (d : ι → Module.End ℂ V), (∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p)) →
    Φ₀ 1 ≠ 0 → Function.Injective Φ₀ := by
  first | exact @GlobalTheory.FockAlg.injective_of_pderiv | exact GlobalTheory.FockAlg.injective_of_pderiv | (intros; apply GlobalTheory.FockAlg.injective_of_pderiv <;> assumption)
