import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLnStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem finite_natDegree_eq {R : Type} [Semiring R] [Finite R] (n : ℕ) :
    {f : R[X] | f.natDegree = n}.Finite := by
  refine Set.Finite.of_finite_image (f := fun p : R[X] => fun i : Fin (n + 1) => p.coeff i)
    (Set.toFinite _) ?_
  intro p hp q hq hpq
  have hp' : p.natDegree = n := hp
  have hq' : q.natDegree = n := hq
  ext i
  by_cases hi : i ≤ n
  · exact congrFun hpq ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem eSerC_eq_sum {g : ℕ} [Fact g.Prime] (L : LabelDatum g) (n : ℕ)
    (hfin : {χ : Gn g n → ℂ | IsIrr χ}.Finite) (f : (ZMod g)[X]) :
    eSerC L n f = ∑ χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f), zOf χ := by
  have hset : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} =
      ↑(hfin.toFinset.filter (fun χ => HasLabel L χ f)) := by
    ext χ
    simp [Set.Finite.mem_toFinset]
  rw [eSerC, hset, finsum_mem_coe_finset]

theorem eSerC_laws : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ n : ℕ, (∀ f, eSerC L n f * eSerC L n f = eSerC L n f) ∧ (∀ f a, eSerC L n f * a = a * eSerC L n f) ∧ (∀ f f', f ≠ f' → eSerC L n f * eSerC L n f' = 0) ∧ (∀ f, ¬ (f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) → eSerC L n f = 0) ∧ ∃ S : Finset (ZMod g)[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, eSerC L n f = 1 := by
  intro g _ L hg hG n
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)
  obtain ⟨huniq, hprops, -⟩ := GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG n
  have horth := GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central (Gn g n)
  have he : ∀ f, eSerC L n f = ∑ χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f), zOf χ :=
    fun f => eSerC_eq_sum L n hfin f
  have hmem : ∀ f χ, χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f) ↔ IsIrr χ ∧ HasLabel L χ f := by
    intro f χ
    simp [Set.Finite.mem_toFinset]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [he f, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hχi := ((hmem f χ).1 hχ).1
    rw [Finset.sum_congr rfl fun χ' hχ' => (horth χ χ' hχi ((hmem f χ').1 hχ').1).1,
      Finset.sum_ite_eq, if_pos hχ]
  · intro f a
    rw [he f, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ hχ =>
      (horth χ χ ((hmem f χ).1 hχ).1 ((hmem f χ).1 hχ).1).2.1 a
  · intro f f' hff'
    rw [he f, he f', Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun χ hχ => Finset.sum_eq_zero fun χ' hχ' => ?_
    obtain ⟨hi, hl⟩ := (hmem f χ).1 hχ
    obtain ⟨hi', hl'⟩ := (hmem f' χ').1 hχ'
    rw [(horth χ χ' hi hi').1, if_neg]
    rintro rfl
    exact hff' ((huniq χ hi).unique hl hl')
  · intro f hf
    rw [he f]
    exact Finset.sum_eq_zero fun χ hχ => absurd (hprops χ f ((hmem f χ).1 hχ).2) hf
  · have hS := finite_natDegree_eq (R := ZMod g) n
    have hSmem : ∀ f, f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0) ↔
        f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 := by
      intro f
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      tauto
    refine ⟨_, hSmem, ?_⟩
    calc ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0), eSerC L n f
        = ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0),
            ∑ χ ∈ hfin.toFinset, if HasLabel L χ f then zOf χ else 0 := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [he f, Finset.sum_filter]
      _ = ∑ χ ∈ hfin.toFinset, ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0),
            if HasLabel L χ f then zOf χ else 0 := Finset.sum_comm
      _ = ∑ χ ∈ hfin.toFinset, zOf χ := by
          refine Finset.sum_congr rfl fun χ hχ => ?_
          have hi : IsIrr χ := hfin.mem_toFinset.1 hχ
          obtain ⟨f0, hf0, hu⟩ := huniq χ hi
          rw [Finset.sum_eq_single f0]
          · rw [if_pos hf0]
          · intro b _ hb
            rw [if_neg]
            exact fun h => hb (hu b h)
          · intro h0
            exact absurd ((hSmem f0).2 (hprops χ f0 hf0)) h0
      _ = 1 := by
          rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
          exact hsum

end GlobalTheory.GLq
