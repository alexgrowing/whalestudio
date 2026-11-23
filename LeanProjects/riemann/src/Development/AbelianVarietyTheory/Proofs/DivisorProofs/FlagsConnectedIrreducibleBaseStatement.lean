import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsConnectedIrreducibleBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.FlagConnect
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flags_connected_irreducible_base : ∀ (L : Type) [Field L] (B : Scheme.{0}) (s : Spec (CommRingCat.of L) ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (G₁ G₂ : ∀ a, Vert.Flag ((Scheme.Modules.pullback s).obj (E a)) (r a)), ∃ (T : Scheme.{0}) (g : T ⟶ B) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (G : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)) (v₁ : t₁ ≫ g = s) (v₂ : t₂ ≫ g = s), IrreducibleSpace T ∧ Carries g E r G t₁ s v₁ G₁ ∧ Carries g E r G t₂ s v₂ G₂ := by
  first | exact @GlobalTheory.FlagPath.exists_irreducible_family | exact GlobalTheory.FlagPath.exists_irreducible_family | (intros; apply GlobalTheory.FlagPath.exists_irreducible_family <;> assumption)
