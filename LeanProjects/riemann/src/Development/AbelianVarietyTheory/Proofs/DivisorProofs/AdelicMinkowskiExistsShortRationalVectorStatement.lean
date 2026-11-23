import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMinkowskiExistsShortRationalVector
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_minkowski_exists_short_rational_vector : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∃ B : Set (Fin n → AF F), IsCompact B ∧ ∀ g : Matrix (Fin n) (Fin n) (AF F), IsUnit g.det → (∃ u : (AF F)ˣ, (u : AF F) = g.det ∧ (GroundTheory.Global.IdeleGroup.ideleModule F u : ℝ) ≤ 1) → ∃ ξ : Fin n → F, ξ ≠ 0 ∧ g *ᵥ (fun i => algebraMap F (AF F) (ξ i)) ∈ B := by
  first | exact @GlobalTheory.AdelicMinkowski.exists_compact_mulVec_rat_mem | exact GlobalTheory.AdelicMinkowski.exists_compact_mulVec_rat_mem | (intros; apply GlobalTheory.AdelicMinkowski.exists_compact_mulVec_rat_mem <;> assumption)
