import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetSubspace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_set_subspace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁),
    (0 ∈ lagSetB M M₁ H H') ∧ (∀ l ∈ lagSetB M M₁ H H', ∀ l' ∈ lagSetB M M₁ H H', l + l' ∈ lagSetB M M₁ H H') ∧
    ∀ t : ℝ, ∀ l ∈ lagSetB M M₁ H H', t • l ∈ lagSetB M M₁ H H' := by
  first | exact @GlobalTheory.ArchSchB.lagSetB_isSubspace | exact GlobalTheory.ArchSchB.lagSetB_isSubspace | (intros; apply GlobalTheory.ArchSchB.lagSetB_isSubspace <;> assumption)
