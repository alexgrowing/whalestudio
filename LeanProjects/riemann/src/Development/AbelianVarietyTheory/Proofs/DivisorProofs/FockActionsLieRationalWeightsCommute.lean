import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_lie_wts_comm : ∀ P Q R S : ℕ, IsLieAct (fockAct1 P Q R S) ∧ IsLieAct (fockAct2 P Q R S) ∧
    (∀ v, v ∈ ⨆ μ : Ix P Q → ℚ, wtSub (fockAct1 P Q R S) μ) ∧ (∀ v, v ∈ ⨆ μ : Ix R S → ℚ, wtSub (fockAct2 P Q R S) μ) ∧
    ∀ X Y f, fockAct1 P Q R S X (fockAct2 P Q R S Y f) = fockAct2 P Q R S Y (fockAct1 P Q R S X f) := by
  intro P Q R S
  obtain ⟨h1, h2, hc⟩ := GlobalTheory.FockPair.pair_lie_commute P Q R S
  obtain ⟨w1, w2⟩ := GlobalTheory.FockPolGK.pol_locFin_weights P Q R S
  refine ⟨h1, h2, fun v => (w1 v).2, fun v => (w2 v).2, fun X Y f => ?_⟩
  have := LinearMap.congr_fun (hc X Y) f
  simpa only [Module.End.mul_apply] using this

end GlobalTheory.HoweR
