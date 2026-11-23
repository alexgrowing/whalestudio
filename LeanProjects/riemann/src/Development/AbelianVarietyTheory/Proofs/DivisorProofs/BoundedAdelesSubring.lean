import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

noncomputable section

namespace GlobalTheory.BddAdeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_bddA_of_le {S T : Finset (Pl F)} {c C : ℝ≥0} (hST : S ⊆ T) (hc : c ≤ C) (h1 : 1 ≤ C)
    {z : AE F E} (hz : z ∈ bddA E S c) : z ∈ bddA E T C := by
  refine ⟨fun v => (hz.1 v).trans ?_, fun w τ => (hz.2 w τ).trans hc⟩
  by_cases hv : v ∈ S
  · rw [if_pos hv, if_pos (hST hv)]; exact hc
  · rw [if_neg hv]; split_ifs
    · exact h1
    · exact le_rfl

theorem zero_mem_bddA (S : Finset (Pl F)) (c : ℝ≥0) : (0 : AE F E) ∈ bddA E S c :=
  ⟨fun v => by rw [map_zero, absFin_zero]; exact bot_le, fun w τ => by simp⟩

theorem one_mem_bddA : (1 : AE F E) ∈ bddA E (∅ : Finset (Pl F)) 1 :=
  ⟨fun v => by rw [map_one, absFin_one]; split_ifs <;> exact le_rfl, fun w τ => by simp⟩

theorem neg_mem_bddA {S : Finset (Pl F)} {c : ℝ≥0} {z : AE F E} (hz : z ∈ bddA E S c) :
    -z ∈ bddA E S c :=
  ⟨fun v => by rw [map_neg, absFin_neg]; exact hz.1 v,
    fun w τ => by rw [map_neg, map_neg, nnnorm_neg]; exact hz.2 w τ⟩

theorem add_mem_bddA {S : Finset (Pl F)} {c : ℝ≥0} {x y : AE F E} (hx : x ∈ bddA E S c)
    (hy : y ∈ bddA E S c) : x + y ∈ bddA E S (c + c) := by
  refine ⟨fun v => ?_, fun w τ => ?_⟩
  · rw [map_add]
    refine (absFin_add_le F v _ _).trans ((max_le (hx.1 v) (hy.1 v)).trans ?_)
    split_ifs
    · exact le_add_self
    · exact le_rfl
  · rw [map_add, map_add]
    exact (nnnorm_add_le _ _).trans (add_le_add (hx.2 w τ) (hy.2 w τ))

theorem mul_mem_bddA {S : Finset (Pl F)} {c : ℝ≥0} {x y : AE F E} (hx : x ∈ bddA E S c)
    (hy : y ∈ bddA E S c) : x * y ∈ bddA E S (c * c) := by
  refine ⟨fun v => ?_, fun w τ => ?_⟩
  · rw [map_mul]
    refine (absFin_mul_le F v _ _).trans ((mul_le_mul' (hx.1 v) (hy.1 v)).trans ?_)
    split_ifs
    · exact le_rfl
    · rw [one_mul]
  · rw [map_mul, map_mul, nnnorm_mul]
    exact mul_le_mul' (hx.2 w τ) (hy.2 w τ)

open Classical in
variable (F E) in

def bddSubring (ι : Type) : Subring (ι → AE F E) where
  carrier := Bdd F E ι
  zero_mem' := ⟨∅, 0, fun _ => zero_mem_bddA _ _⟩
  one_mem' := ⟨∅, 1, fun _ => one_mem_bddA⟩
  add_mem' := by
    rintro f g ⟨S, c, hf⟩ ⟨S', c', hg⟩
    refine ⟨S ∪ S', (max c c' + 1) + (max c c' + 1), fun t => add_mem_bddA ?_ ?_⟩
    · exact mem_bddA_of_le Finset.subset_union_left ((le_max_left _ _).trans le_self_add) le_add_self (hf t)
    · exact mem_bddA_of_le Finset.subset_union_right ((le_max_right _ _).trans le_self_add) le_add_self (hg t)
  mul_mem' := by
    rintro f g ⟨S, c, hf⟩ ⟨S', c', hg⟩
    refine ⟨S ∪ S', (max c c' + 1) * (max c c' + 1), fun t => mul_mem_bddA ?_ ?_⟩
    · exact mem_bddA_of_le Finset.subset_union_left ((le_max_left _ _).trans le_self_add) le_add_self (hf t)
    · exact mem_bddA_of_le Finset.subset_union_right ((le_max_right _ _).trans le_self_add) le_add_self (hg t)
  neg_mem' := by
    rintro f ⟨S, c, hf⟩
    exact ⟨S, c, fun t => neg_mem_bddA (hf t)⟩

theorem exists_subring_eq_bdd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : Type) : ∃ R : Subring (ι → AE F E), (R : Set (ι → AE F E)) = Bdd F E ι :=
  ⟨bddSubring F E ι, rfl⟩

end GlobalTheory.BddAdeleRing

end
