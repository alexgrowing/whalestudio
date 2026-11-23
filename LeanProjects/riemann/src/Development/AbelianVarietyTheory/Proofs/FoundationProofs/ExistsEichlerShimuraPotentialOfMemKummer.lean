import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerPotentialRelationPadicStatement

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem GlobalTheory.KZ.exists_pot_rel_of_mem_bSet : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F := by
  intro Ω _ _ _ ε X _ hj N l w hl h2 hN hc hw b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨φ, hφ, hφ'⟩ := hj
  exact GlobalTheory.T.exists_kummerPotentialRelation_padic Ω ε X l ⟨φ, hφ', hφ⟩ N w (by omega) h2
    ((Nat.Prime.coprime_iff_not_dvd hl.out).1 hc.symm) hw b (Submodule.subset_span hb)
