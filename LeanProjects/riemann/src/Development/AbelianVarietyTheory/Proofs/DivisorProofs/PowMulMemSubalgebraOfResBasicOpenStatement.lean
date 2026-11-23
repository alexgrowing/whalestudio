import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulMemSubalgebraOfResBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemAdjoinOfLocalizationAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdjoinRestrictedSectionsOfLocalStatement
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  first | exact @GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen | exact GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen | (intros; apply GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen <;> assumption)
