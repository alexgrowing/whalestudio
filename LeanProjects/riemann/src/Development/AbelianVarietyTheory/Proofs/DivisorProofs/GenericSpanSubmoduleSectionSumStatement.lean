import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSpanSubmoduleSectionSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_span_submodule_section_sum : ∀ {X : Scheme.{0}} [IsIntegral X] {F : X.Modules} {κ : Type} [Fintype κ] {V : X.Opens} (c : κ → Γ(F, V)), IsFrame c →
    ∀ (Q : κ → Prop) (N : Submodule X.functionField (genStalk F)),
    (∀ hV : genericPoint X ∈ V, N = Submodule.span X.functionField ((fun z => F.presheaf.germ V _ hV (c z)) '' {z | Q z})) →
    ∀ (V' : X.Opens) (h : V' ≤ V) (a : κ → Γ(X, V')),
      (∑ z, a z • resM F h (c z)) ∈ (Sub.ofGeneric N).sec V' ↔ ∀ z, ¬ Q z → a z = 0 := by
  first | exact @GlobalTheory.GrFilt.mem_ofGeneric_iff_of_span | exact GlobalTheory.GrFilt.mem_ofGeneric_iff_of_span | (intros; apply GlobalTheory.GrFilt.mem_ofGeneric_iff_of_span <;> assumption)
