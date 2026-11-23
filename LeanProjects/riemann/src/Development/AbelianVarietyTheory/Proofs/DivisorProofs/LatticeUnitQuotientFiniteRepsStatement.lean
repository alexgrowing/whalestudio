import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeUnitQuotientFiniteReps
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjNeZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_unit_quotient_finite_reps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d) (v : Pl F)
    (u : AF F), W.L.IsLattice E → evI F u = 0 → (∀ w : Pl F, w ≠ v → evFin F w u = 0) →
    evFin F v u ∈ v.adicCompletionIntegers F → ∀ m : ℕ, m ≠ 0 →
    ∃ S : Finset (Fin d → AE F E), (∀ s ∈ S, s ∈ latHat W) ∧
      ∀ z ∈ latHat W, ∃ s ∈ S, ∃ y ∈ latHat W, u • z - s = m • y := by
  first | exact @GlobalTheory.SphLineComm.smul_latHat_finite_mod | exact GlobalTheory.SphLineComm.smul_latHat_finite_mod | (intros; apply GlobalTheory.SphLineComm.smul_latHat_finite_mod <;> assumption)
