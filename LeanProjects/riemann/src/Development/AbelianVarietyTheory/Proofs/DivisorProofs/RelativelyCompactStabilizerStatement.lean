import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatively_compact_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s → ∃ C : Set (UA σ X.J), IsCompact C ∧ ((GlobalTheory.StabHaar.stabK B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) ⊆ C := by
  first | exact @GlobalTheory.StabBounded.exists_compact_superset_stabK | exact GlobalTheory.StabBounded.exists_compact_superset_stabK | (intros; apply GlobalTheory.StabBounded.exists_compact_superset_stabK <;> assumption)
