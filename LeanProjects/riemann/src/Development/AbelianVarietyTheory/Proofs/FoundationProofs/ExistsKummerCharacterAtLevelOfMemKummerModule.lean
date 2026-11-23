import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongrStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterOfUpperHalfPlaneRootStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUnStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem GlobalTheory.KZ.H3.exists_kum_of_mem_A : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime], JHol X → ∀ (n : ℕ), ∀ x ∈ X.A l, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  intro Ω _ _ ε X l _ hJ n x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, he⟩ := hy n
    have hm : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    obtain ⟨a, b, hab⟩ := GlobalTheory.T.exists_isRoot_of_mem_Un_of_jHol Ω ε X hJ (l ^ n) hm f hf
    exact GlobalTheory.T.exists_kummerCharacter_of_upperHalfPlane_root Ω ε X l n y f a b he hab
  | zero => exact ⟨0, (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1⟩
  | add y z _ _ hy hz =>
    obtain ⟨χ, hχ⟩ := hy
    obtain ⟨χ', hχ'⟩ := hz
    exact ⟨χ + χ', (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 y z χ χ' hχ hχ'⟩
  | smul c y _ hy =>
    obtain ⟨χ, hχ⟩ := hy
    exact ⟨_, GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n c y χ hχ⟩
