import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameImageSpansGenericStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_image_spans_generic_stalk : ∀ {X : Scheme.{0}} [IsIntegral X] {E E' : X.Modules} {n : ℕ} (u : E ⟶ E'), Mono u → ∀ {V : X.Opens} (f : Fin n → Γ(E, V))
    (f' : Fin n → Γ(E', V)), IsFrame f → IsFrame f' → ∀ hV : genericPoint X ∈ V,
    Submodule.span X.functionField (Set.range fun i => (E'.presheaf.germ V _ hV ((u.app V (f i))) : genStalk E')) = ⊤ := by
  first | exact @GlobalTheory.span_germ_map_frame_eq_top_of_mono | exact GlobalTheory.span_germ_map_frame_eq_top_of_mono | (intros; apply GlobalTheory.span_germ_map_frame_eq_top_of_mono <;> assumption)
