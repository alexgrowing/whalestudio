import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSL2Adeles
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_SL2_adeles : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : Matrix (Fin 2) (Fin 2) (AF F), g.det = 1 → g ∈ closure {x : Matrix (Fin 2) (Fin 2) (AF F) | ∃ γ : Matrix (Fin 2) (Fin 2) F, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) (AF F), h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map (algebraMap F (AF F)) * h} := by
  first | exact @GlobalTheory.StrongApproximationSL2.strongApprox_SL2 | exact GlobalTheory.StrongApproximationSL2.strongApprox_SL2 | (intros; apply GlobalTheory.StrongApproximationSL2.strongApprox_SL2 <;> assumption)
