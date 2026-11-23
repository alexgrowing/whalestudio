import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFramesFiltrationGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frames_filtration_generic : ∀ {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}
    (o : ι → ℕ), Function.Injective o → ∀ (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) {V : X.Opens}
    (f : ∀ a, Fin (r a) → Γ(E a, V)), (∀ a, IsFrame (f a)) → ∀ (f' : ∀ a, Fin (r a) → Γ(E' a, V)) (hf' : ∀ a, IsFrame (f' a))
    (c : (Σ a, Fin (r a)) → Γ(L, V)) (hc : IsFrame c), AdaptedAt o T u f f' hf' c hc → ∀ hV : genericPoint X ∈ V,
    (∀ a, Submodule.span X.functionField
      (Set.range fun i => ((E' a).presheaf.germ V _ hV ((u a).app V (f a i)) : genStalk (E' a))) = ⊤) →
    ∀ k, genSpan o T k = Submodule.span X.functionField ((fun z => L.presheaf.germ V _ hV (c z)) '' {z | o z.1 < k}) := by
  first | exact @GlobalTheory.GrFilt.genSpan_eq_of_adaptedAt | exact GlobalTheory.GrFilt.genSpan_eq_of_adaptedAt | (intros; apply GlobalTheory.GrFilt.genSpan_eq_of_adaptedAt <;> assumption)
