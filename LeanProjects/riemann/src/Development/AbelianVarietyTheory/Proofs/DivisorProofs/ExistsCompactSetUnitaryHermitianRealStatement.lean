import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetUnitaryHermitianReal
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_set_unitary_hermitian_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ u : Fin M → K ⊗[F] E, hR K σ J u u = 0 → u = 0) → ∃ C : Set (K ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (K ⊗[F] E), Formalism.UG.cT (sigR K σ) g * JR K J * g = JR K J → ∀ i j, g i j ∈ C := by
  first | exact @GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic | exact GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic | (intros; apply GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic <;> assumption)
