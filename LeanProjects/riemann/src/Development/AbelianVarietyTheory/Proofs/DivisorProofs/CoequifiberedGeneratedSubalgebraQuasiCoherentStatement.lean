import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoequifiberedGeneratedSubalgebraQuasiCoherent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j)))), (∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) → (subNat F α V T).Coequifibered := by
  first | exact @GlobalTheory.QcSub.coequifibered_subNat | exact GlobalTheory.QcSub.coequifibered_subNat | (intros; apply GlobalTheory.QcSub.coequifibered_subNat <;> assumption)
