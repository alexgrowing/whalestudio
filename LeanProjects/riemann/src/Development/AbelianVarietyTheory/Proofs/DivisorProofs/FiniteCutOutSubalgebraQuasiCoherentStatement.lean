import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCutOutSubalgebraQuasiCoherent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleFgOfLocallyLeFgStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLocalizationAwaySpanFinsetStatement
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral) → ∀ {ι : Type} (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → (∀ x : X, ∃ j, x ∈ V j) → ∀ (T : ∀ j, Set (F.obj (op (V j)))), (∀ j, (T j).Finite) → ∀ W : X.Opens, IsAffineOpen W → (subMap F α V T W).Finite := by
  first | exact @GlobalTheory.QcSub.subMap_finite | exact GlobalTheory.QcSub.subMap_finite | (intros; apply GlobalTheory.QcSub.subMap_finite <;> assumption)
