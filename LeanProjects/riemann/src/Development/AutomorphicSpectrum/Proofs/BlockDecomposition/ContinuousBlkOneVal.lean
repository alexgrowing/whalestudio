import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.UnipLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_one_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 X)⁻¹ = blk h w 1 (-X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simpa using GlobalTheory.LeviFubini.blk_one_zero h w

theorem blk_one_corner {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (i : Fin a) (j : Fin b) :
    (blk h w 1 X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j)) = X i j := by
  rw [CtLevel.blk_val]
  simp

theorem continuous_blk_one_val {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (blk h w 1 X).val := by
  refine continuous_matrix fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  simp only [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · simpa using continuous_const
  · simpa using continuous_id.matrix_elem i j
  · simpa using continuous_const
  · simpa using continuous_const

theorem continuous_blk_one {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => blk h w 1 X := by
  refine Units.continuous_iff.2 ⟨continuous_blk_one_val h w, ?_⟩
  have e : (fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (((blk h w 1 X)⁻¹ : GLw n w)).val) =
      (fun X => (blk h w 1 X).val) ∘ fun X => -X := by
    funext X
    simp [blk_one_inv]
  exact e ▸ (continuous_blk_one_val h w).comp continuous_neg

def intSub (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) where
  carrier := {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}
  one_mem' := fun i j => by simp
  mul_mem' := fun {X Y} hX hY i j => by
    simpa using (Valued.v.map_add _ _).trans (max_le (hX i j) (hY i j))
  inv_mem' := fun {X} hX i j => by simpa using hX i j

theorem intMat_eq_intSub (a b : ℕ) (w : Pl E) : intMat a b w = intSub a b w := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun X hX => hX) fun X hX => Subgroup.subset_closure hX

theorem isCompact_intSub (a b : ℕ) (w : Pl E) :
    IsCompact (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) := by
  have e : (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) =
      Multiplicative.toAdd ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ
        fun _ : Fin b => ((w.adicCompletionIntegers E : Set (w.adicCompletion E)))) := by
    ext X
    exact ⟨fun hX i _ j _ => hX i j, fun hX i j => hX i trivial j trivial⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers w

theorem unip_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ≤ intMat a b w ∧ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).relIndex (intMat a b w) ≠ 0 := by
  intro E _ _ _ a b n h w K' hK' hKK
  have hmem : ∀ X, X ∈ (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ↔
      blk h w 1 (Multiplicative.toAdd X) ∈ K' := fun X => Iff.rfl
  refine ⟨fun X hX => ?_, ?_⟩
  · rw [intMat_eq_intSub]
    intro i j
    obtain ⟨u, hu⟩ := hKK ((hmem X).1 hX)
    have h1 : Valued.v ((blk h w 1 (Multiplicative.toAdd X)).val (CtLevel.blkEq h (Sum.inl i))
        (CtLevel.blkEq h (Sum.inr j))) ≤ 1 := by
      rw [← hu]
      exact (u.val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))).2
    rwa [blk_one_corner] at h1
  · have hopen : IsOpen (((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) :
        Subgroup _) : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) :=
      hK'.preimage ((continuous_blk_one h w).comp continuous_toAdd)
    rw [intMat_eq_intSub]
    haveI : CompactSpace (intSub a b w) := isCompact_iff_compactSpace.1 (isCompact_intSub a b w)
    haveI : Finite ((intSub a b w) ⧸ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).subgroupOf (intSub a b w)) :=
      Subgroup.quotient_finite_of_isOpen _ (hopen.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.UnipLevel
