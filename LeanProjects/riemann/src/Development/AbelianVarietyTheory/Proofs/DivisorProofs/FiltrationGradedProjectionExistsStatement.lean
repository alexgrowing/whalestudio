import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationGradedProjectionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismOfCompatibleFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_graded_projection_exists : ∀ {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}
    (o : ι → ℕ), Function.Injective o → ∀ (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a), (∀ a, Mono (u a)) →
    (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ LocAdapted r o T u V) → FrameMem r o T u → GenSpanEq r o T u →
    ∀ b, ∃ κ : (filtSub o T (o b + 1)).toMod ⟶ E' b, IsProj r o T u b κ := by
  first | exact @GlobalTheory.GrFiltProj.exists_isProj | exact GlobalTheory.GrFiltProj.exists_isProj | (intros; apply GlobalTheory.GrFiltProj.exists_isProj <;> assumption)
