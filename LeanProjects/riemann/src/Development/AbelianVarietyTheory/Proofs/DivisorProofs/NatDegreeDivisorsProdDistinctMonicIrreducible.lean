import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible

theorem exists_subset_natDegree_of_dvd_prod {k : Type} [Field k] {ι : Type} (P : ι → k[X])
    (hP : ∀ c, Irreducible (P c)) (s : Finset ι) :
    ∀ q : k[X], q ∣ ∏ c ∈ s, P c → ∃ A : Finset ι, A ⊆ s ∧ ∑ c ∈ A, (P c).natDegree = q.natDegree := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro q hq
    rw [Finset.prod_empty] at hq
    exact ⟨∅, Finset.Subset.refl _, by
      rw [Finset.sum_empty, natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hq)]⟩
  | insert i s hi ih =>
    intro q hq
    have hne : ∏ c ∈ insert i s, P c ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun c _ => (hP c).ne_zero
    have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero hne hq
    rw [Finset.prod_insert hi] at hq
    obtain ⟨q₁, q₂, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hq
    obtain ⟨A, hA, hsum⟩ := ih q₂ h2
    have hq1 : q₁ ≠ 0 := left_ne_zero_of_mul hq0
    have hq2 : q₂ ≠ 0 := right_ne_zero_of_mul hq0
    rw [natDegree_mul hq1 hq2]
    rcases (hP i).dvd_iff.mp h1 with hu | ha
    · exact ⟨A, hA.trans (Finset.subset_insert _ _), by
        rw [hsum, natDegree_eq_zero_of_isUnit hu, zero_add]⟩
    · refine ⟨insert i A, Finset.insert_subset_insert _ hA, ?_⟩
      rw [Finset.sum_insert (fun h => hi (hA h)), hsum,
        natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)]

theorem natDegree_divisors_prod :
    ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (P : ι → k[X]), (∀ c, (P c).Monic ∧ Irreducible (P c)) → Function.Injective P → (∀ a : ℕ, (∃ q : k[X], q ∣ ∏ c, P c ∧ q.natDegree = a) ↔ ∃ A : Finset ι, ∑ c ∈ A, (P c).natDegree = a) ∧ ∀ Q : ℕ → Prop, (∃ q : k[X], Irreducible q ∧ q ∣ ∏ c, P c ∧ Q q.natDegree) ↔ ∃ c, Q (P c).natDegree := by
  intro k _ ι _ P hP _
  refine ⟨fun a => ⟨?_, ?_⟩, fun Q => ⟨?_, ?_⟩⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨A, -, hA⟩ := exists_subset_natDegree_of_dvd_prod P (fun c => (hP c).2) _ q hq
    exact ⟨A, hA⟩
  · rintro ⟨A, rfl⟩
    exact ⟨∏ c ∈ A, P c, Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _),
      natDegree_prod_of_monic _ _ fun c _ => (hP c).1⟩
  · rintro ⟨q, hirr, hq, hQ⟩
    obtain ⟨c, -, hc⟩ := (Prime.dvd_finset_prod_iff hirr.prime _).mp hq
    have ha := hirr.associated_of_dvd (hP c).2 hc
    refine ⟨c, ?_⟩
    rwa [← natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)]
  · rintro ⟨c, hc⟩
    exact ⟨P c, (hP c).2, Finset.dvd_prod_of_mem _ (Finset.mem_univ c), hc⟩

end GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible
