import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem finiteDimensional_Ks_of_finExt {l : ℕ} [Fact l.Prime] (K : FinExt l) (s : ℕ) :
    FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h0 : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  have hfin : Finite ↥{x : Om l | x ^ (l ^ s) = 1} := by
    apply Set.Finite.to_subtype
    refine (Multiset.finite_toSet (Polynomial.nthRoots (l ^ s) (1 : Om l))).subset ?_
    intro x hx
    exact (Polynomial.mem_nthRoots hpos).2 hx
  have h1 : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  unfold Ks
  exact IntermediateField.finiteDimensional_sup _ _

theorem exists_good_situation (l : ℕ) [Fact l.Prime] :
    ∀ (K : FinExt l) (s : ℕ), 1 ≤ s → (l = 2 → 2 ≤ s) → K.1 ≤ Ks K s →
      ∃ L0 : FinExt l, ∀ LL : FinExt l, L0.1 ≤ LL.1 → Good K s LL := by
  intro K s h1 h2 h3
  have := finiteDimensional_Ks_of_finExt K s
  refine ⟨⟨IntermediateField.normalClosure ℚ_[l] ↥(Ks K s) (Om l), inferInstance⟩,
    fun LL hL => ⟨h1, h2, h3, fun τ x => hL ?_⟩⟩
  exact AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩

end GlobalTheory.MemLoc
