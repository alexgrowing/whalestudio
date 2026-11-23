import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfRefinement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreimageTranslate
open AlgebraicGeometry CategoryTheory GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCechOneCoboundary_of_refinement : ∀ {Y : Scheme.{0}} {I J : Type} (Uc : I → Y.Opens) (c : GlobalTheory.KS.C1 Uc), GlobalTheory.KS.IsCoc Uc c → ∀ (V : J → Y.Opens) (σ : J → I), (∀ p, V p ≤ Uc (σ p)) → (⨆ p, V p = ⊤) → ∀ (B : ∀ p, Γ(Y, V p)), (∀ p p', GlobalTheory.KS.rsT (c (σ p) (σ p')) (V p ⊓ V p') = GlobalTheory.KS.rsT (B p') (V p ⊓ V p') - GlobalTheory.KS.rsT (B p) (V p ⊓ V p')) → GlobalTheory.KS.IsCob Uc c := by
  first | exact @GlobalTheory.KS.Refine.isCob_of_refine | exact GlobalTheory.KS.Refine.isCob_of_refine | (intros; apply GlobalTheory.KS.Refine.isCob_of_refine <;> assumption)
