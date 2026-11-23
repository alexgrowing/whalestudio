import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem words_of_type (D t : ℕ) (α : Fin D →₀ ℕ) (hα : α.degree ≤ t) :
    ∃ β : Fin t → Fin (D + 1), (∀ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card = α i) ∧
      (α.degree = t → ∀ q, β q ≠ Fin.last D) ∧
      ∀ (M : Type) [Monoid M] (f : Fin (D + 1) → M),
        (List.ofFn fun q => f (β q)).prod =
          (List.ofFn fun i : Fin D => f i.castSucc ^ α i).prod * f (Fin.last D) ^ (t - α.degree) := by
  classical
  have hdeg : α.degree = ∑ i, α i := Finsupp.degree_eq_sum α
  set L : List (Fin (D + 1)) :=
    (List.ofFn fun i : Fin D => List.replicate (α i) i.castSucc).flatten ++
      List.replicate (t - α.degree) (Fin.last D) with hL
  have hlen : L.length = t := by
    simp only [hL, List.length_append, List.length_flatten, List.map_ofFn, List.length_replicate,
      List.sum_ofFn, Function.comp_def]
    omega
  refine ⟨fun q => L.get (Fin.cast hlen.symm q), ?_⟩
  set β : Fin t → Fin (D + 1) := fun q => L.get (Fin.cast hlen.symm q) with hβ
  have hofFn : List.ofFn β = L := by
    apply List.ext_get
    · simp [hlen]
    · intro n h1 h2
      simp [hβ]
  have hcount : ∀ x, (Finset.univ.filter fun q => β q = x).card = L.count x := by
    intro x
    rw [← hofFn, ← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map, Finset.card_def,
      Finset.filter_val]
    congr 1
    apply Multiset.filter_congr
    intro a _
    exact eq_comm
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hcount]
    simp [hL, List.count_flatten, List.count_replicate, Function.comp_def, Fin.castSucc_inj, List.sum_ofFn,
      (Fin.castSucc_ne_last i).symm]
  · intro ht q
    have hmem : β q ∈ L := List.get_mem _ _
    have h0 : t - α.degree = 0 := by omega
    simp only [hL, h0, List.replicate_zero, List.append_nil, List.mem_flatten, List.mem_ofFn] at hmem
    obtain ⟨l, ⟨j, rfl⟩, hl⟩ := hmem
    rw [List.mem_replicate] at hl
    rw [hl.2]
    exact Fin.castSucc_ne_last j
  · intro M _ f
    have : (List.ofFn fun q => f (β q)) = (List.ofFn β).map f := by
      rw [List.map_ofFn]; rfl
    rw [this, hofFn, hL]
    simp [List.prod_append, List.map_flatten, List.prod_flatten, List.map_ofFn, Function.comp_def,
      List.prod_replicate]

end GlobalTheory.HSShort
