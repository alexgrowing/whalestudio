import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupInNeighbourhood
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_in_neighbourhood : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ x, σ (σ x) = x) → ∀ {d : ℕ} (J : Matrix (Fin d) (Fin d) E), ∀ N ∈ 𝓝 (1 : UA σ J),
      ∃ U : Subgroup (UA σ J), IsOpen (U : Set (UA σ J)) ∧
        ∀ k ∈ U, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → k ∈ N := by
  first | exact @GlobalTheory.UnitarySmallSub.exists_open_subgroup_finite_subset | exact GlobalTheory.UnitarySmallSub.exists_open_subgroup_finite_subset | (intros; apply GlobalTheory.UnitarySmallSub.exists_open_subgroup_finite_subset <;> assumption)
