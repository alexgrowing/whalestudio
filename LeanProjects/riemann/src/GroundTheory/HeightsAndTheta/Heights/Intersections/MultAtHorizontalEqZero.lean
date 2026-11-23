import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedG
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraBis
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Lemmas

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isSec_iff_isSectionOn (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) :
    IsSec P A s ↔ IsSectionOn P A s := by
  constructor
  · rintro ⟨a, ha, hdeg, hs⟩
    exact ⟨a, fun k => (hdeg k).symm, ha, hs⟩
  · rintro ⟨a, hdeg, ha, hs⟩
    exact ⟨a, ha, fun k => (hdeg k).symm, hs⟩

omit [∀ k, Fintype (ι k)] in

theorem vecEmpty_eq_elim0 : (![] : Fin 0 → HermLine ι) = Fin.elim0 := Subsingleton.elim _ _

open Classical in

theorem multAt_horizontal_eq_zero {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s)
    (hind : ∀ (I : Family ι) (t : MRing ι), IsSectionOn P A t →
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P Fin.elim0 A t)
    {W₀ : Ideal (MRing ι)} (hW₀ : W₀ ∈ divSupp P s) (hh : IsHorizontal W₀) :
    (multAt (P ⊔ Ideal.span {s}) W₀ : ℝ) = 0 := by
  obtain ⟨a, hdeg, -, -⟩ := hs
  have hprime : W₀.IsPrime := hW₀.1.1.1
  have hle : P ⊔ Ideal.span {s} ≤ W₀ := hW₀.1.1.2
  choose i hi using hW₀.2
  have ht0 : secOf i a ∉ W₀ := secOf_not_mem hprime hi a
  have ht : IsSectionOn P A (secOf i a) :=
    ⟨a, hdeg, isMultiHomog_secOf i a, fun h => ht0 (le_sup_left.trans hle h)⟩
  have hnot : W₀ ∉ divSupp P (secOf i a) := fun h =>
    ht0 (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  let F : ℝ → Family ι := fun c W _ _ => if W = W₀ then c else 0
  have hFt : recR (F 1) P (Fin.elim0 : Fin 0 → HermLine ι) A (secOf i a) =
      recR (F 0) P Fin.elim0 A (secOf i a) := by
    unfold recR
    congr 1
    refine finsum_mem_congr rfl fun W hW => ?_
    have hne : W ≠ W₀ := fun h => hnot (h ▸ hW)
    simp [F, hne]
  have key := (hind (F 1) _ ht).trans (hFt.trans (hind (F 0) _ ht).symm)
  unfold recR at key
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s)] at key
  have hmem : W₀ ∈ (divSupp_finite P s).toFinset := (Set.Finite.mem_toFinset _).mpr hW₀
  have hsum := sub_left_inj.mp key
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single W₀ (fun W _ hne => by simp [F, hne]) (fun h => absurd hmem h)] at hsum
  simpa [F, hh] using hsum

theorem recR_family_eq {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s)
    (hind : ∀ (I : Family ι) (t : MRing ι), IsSectionOn P A t →
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P Fin.elim0 A t)
    (I J : Family ι) :
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR J P Fin.elim0 A s := by
  unfold recR
  congr 1
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · rw [multAt_horizontal_eq_zero hs hind hW hh, zero_mul, zero_mul]
  · simp [hh]

end Lemmas

def IndependenceOfSmoothMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A : HermLine ι) (s t : MRing ι),
    IsArithVar P 1 → IsSmoothHerm A → IsSectionOn P A s → IsSectionOn P A t →
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P (Fin.elim0 : Fin 0 → HermLine ι) A t

theorem IndependenceOfSmoothMetric.of_indep (h : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement) :
    IndependenceOfSmoothMetric.Statement :=
  fun K _ ι _ I P A s t hP _ hs ht => h K ι I P A s t hP hs ht

theorem R1.equiv_smooth :
    (IndependenceOfSmoothMetric.Statement ∧ GroundTheory.Heights₂.Heights.Inter.RegularityAdditive.Statement) ↔ R1.Statement := by
  constructor
  · rintro ⟨hind, hadd⟩ K _ ι _ P hP
    refine ⟨fun I J A s s' hA hs hs' => ?_, fun I A B s t hA hB hs ht => ?_⟩
    · rw [isSec_iff_isSectionOn] at hs hs'
      simp only [vecEmpty_eq_elim0, rhsR.equiv]
      rw [recR_family_eq hs (fun F t ht => hind K ι F P A s t hP hA hs ht) I J]
      exact hind K ι J P A s s' hP hA hs hs'
    · rw [isSec_iff_isSectionOn] at hs ht
      simp only [vecEmpty_eq_elim0, rhsR.equiv]
      exact hadd K ι I P A B s t hP hA hB hs ht
  · intro h
    refine ⟨fun K _ ι _ I P A s t hP hA hs ht => ?_, fun K _ ι _ I P A B s t hP hA hB hs ht => ?_⟩
    · have := (h K ι P hP).1 I I A s t hA ((isSec_iff_isSectionOn _ _ _).mpr hs)
        ((isSec_iff_isSectionOn _ _ _).mpr ht)
      simpa only [vecEmpty_eq_elim0, rhsR.equiv] using this
    · have := (h K ι P hP).2 I A B s t hA hB ((isSec_iff_isSectionOn _ _ _).mpr hs)
        ((isSec_iff_isSectionOn _ _ _).mpr ht)
      simpa only [vecEmpty_eq_elim0, rhsR.equiv] using this

theorem R1.of_first
    (h : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement ∧ GroundTheory.Heights₂.Heights.Inter.RegularityAdditive.Statement) :
    R1.Statement :=
  R1.equiv_smooth.mp ⟨IndependenceOfSmoothMetric.of_indep h.1, h.2⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
