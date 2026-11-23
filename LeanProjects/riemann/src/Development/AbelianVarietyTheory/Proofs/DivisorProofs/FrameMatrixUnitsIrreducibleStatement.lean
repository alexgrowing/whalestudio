import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMatrixUnitsIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrix_units_irreducible : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (n : ι → ℕ) (A : ∀ a, Matrix (Fin (n a)) (Fin (n a)) L), (∀ a, IsUnit (A a).det) → ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (_ : t₁ ≫ c = 𝟙 _) (_ : t₂ ≫ c = 𝟙 _) (B : ∀ a, Matrix (Fin (n a)) (Fin (n a)) Γ(T, ⊤)), IrreducibleSpace T ∧ (∀ a, IsUnit (B a)) ∧ (∀ a i j, t₁.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv ((1 : Matrix (Fin (n a)) (Fin (n a)) L) i j)) ∧ (∀ a i j, t₂.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv (A a i j)) := by
  first | exact @GlobalTheory.GLPath.exists_path | exact GlobalTheory.GLPath.exists_path | (intros; apply GlobalTheory.GLPath.exists_path <;> assumption)
