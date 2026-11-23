import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem natCard_algHom_intermediateField_of_range_le {F E A : Type} [Field F] [Field E] [Field A]
    [Algebra F E] [Algebra F A] [FiniteDimensional F E] [Algebra.IsSeparable F E] [IsAlgClosed A]
    (M : IntermediateField F A) (h : ∀ (f : E →ₐ[F] A) (x : E), f x ∈ M) :
    Nat.card (E →ₐ[F] ↥M) = finrank F E := by

  have e : (E →ₐ[F] ↥M) ≃ (E →ₐ[F] A) :=
    { toFun := fun g => M.val.comp g
      invFun := fun f => f.codRestrict M.toSubalgebra (h f)
      left_inv := fun _ => AlgHom.ext fun _ => rfl
      right_inv := fun _ => AlgHom.ext fun _ => rfl }
  rw [Nat.card_congr e]
  exact AlgHom.natCard_of_splits F E A fun _ => IsAlgClosed.splits _

private theorem exists_fd_intermediateField_contains_embeddings (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ N : IntermediateField ℚ_[l] (Om l), FiniteDimensional ℚ_[l] ↥N ∧
      ∀ (f : E →ₐ[ℚ_[l]] Om l) (x : E), f x ∈ N := by
  have hfin : ∀ f : E →ₐ[ℚ_[l]] Om l, FiniteDimensional ℚ_[l] ↥f.fieldRange :=
    fun f => f.toLinearMap.finiteDimensional_range
  exact ⟨⨆ f : E →ₐ[ℚ_[l]] Om l, f.fieldRange,
    IntermediateField.finiteDimensional_iSup_of_finite,
    fun f x => (le_iSup (fun g : E →ₐ[ℚ_[l]] Om l => g.fieldRange) f) ⟨x, rfl⟩⟩

theorem exists_finExt_embedding_splitting (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type)
    [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] :
    ∃ LL' : FinExt l, Nonempty (LL →ₐ[ℚ_[l]] ↥LL'.1) ∧
      Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥K.1 ∧
      Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥(K0 K) := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := Module.Finite.left ℚ_[l] ↥(K0 K) ↥K.1
  obtain ⟨N1, hN1, hK1⟩ := exists_fd_intermediateField_contains_embeddings l ↥K.1
  obtain ⟨N0, hN0, hK0⟩ := exists_fd_intermediateField_contains_embeddings l ↥(K0 K)

  let φ : LL →ₐ[ℚ_[l]] Om l := IsAlgClosed.lift
  have : FiniteDimensional ℚ_[l] ↥φ.fieldRange := φ.toLinearMap.finiteDimensional_range

  refine ⟨⟨φ.fieldRange ⊔ N1 ⊔ N0, inferInstance⟩,
    ⟨φ.codRestrict (φ.fieldRange ⊔ N1 ⊔ N0).toSubalgebra fun x => ?_⟩, ?_, ?_⟩
  · exact (le_sup_left.trans le_sup_left : φ.fieldRange ≤ _) ⟨x, rfl⟩
  · exact natCard_algHom_intermediateField_of_range_le _ fun f x =>
      (le_sup_right.trans le_sup_left : N1 ≤ _) (hK1 f x)
  · exact natCard_algHom_intermediateField_of_range_le _ fun f x =>
      (le_sup_right : N0 ≤ _) (hK0 f x)

end GlobalTheory
