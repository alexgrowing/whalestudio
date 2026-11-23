import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.HighUnitsLocal
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.EqZeroOfBrauerLocalApplyEqZero
import GroundTheory.ProfiniteCohomology.GlobalClassFormation
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global FiniteSubfield DirectSum

noncomputable section

variable {K : FiniteSubfield}

theorem bijective_unitsToIdeles_of_four_le {r : ℕ} (hr : 4 ≤ r) :
    Function.Bijective (unitsToIdeles K r).hom := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hC : ∀ m, 3 ≤ m → ∀ c : cohomology (classLimitRep K) m, c = 0 := fun m hm c =>
    (subsingleton_cohomology_classLimitRep_of_three_le K hm).elim c 0
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_classesToUnits_eq K n x hx
    rw [hC n (by omega) c, map_zero]
  · exact exists_unitsToIdeles_eq K (n + 1) y (hC _ (by omega) _)

theorem subsingleton_localGaloisCohomology_of_not_isReal {r : ℕ} (hr : 3 ≤ r) :
    ∀ v : Place K.1, (∀ w : InfinitePlace K.1, v = .inl w → w.IsComplex) →
      Subsingleton (localGaloisCohomology K r v)
  | .inl w, h => subsingleton_localGaloisCohomology_inl_of_isComplex w (h w rfl) (by omega)
  | .inr v, _ => subsingleton_localGaloisCohomology_inr_of_three_le v hr

def realLocalization (ι : LocalEmbeddings K) {r : ℕ} (hr : 1 ≤ r) :
    cohomology (unitsLimitRep K) r →+
      ∀ v : {v : InfinitePlace K.1 // v.IsReal}, localGaloisCohomology K r (.inl v.1) where
  toFun x v := idelesLimitCohomologyEquiv ι hr ((unitsToIdeles K r).hom x) (.inl v.1)
  map_zero' := by
    funext v
    simp only [map_zero]
    rfl
  map_add' x y := by
    funext v
    simp only [map_add]
    rfl

theorem bijective_realComponents {r : ℕ} (hr : 3 ≤ r) :
    Function.Bijective (fun (ζ : ⨁ v : Place K.1, localGaloisCohomology K r v)
      (v : {v : InfinitePlace K.1 // v.IsReal}) => ζ (.inl v.1)) := by
  classical
  refine ⟨fun ζ ζ' h => ?_, fun f => ?_⟩
  · ext v
    rcases v with w | v
    · by_cases hw : w.IsReal
      · exact congrFun h ⟨w, hw⟩
      · have := subsingleton_localGaloisCohomology_inl_of_isComplex w
          (InfinitePlace.not_isReal_iff_isComplex.1 hw) (r := r) (by omega)
        exact Subsingleton.elim _ _
    · have := subsingleton_localGaloisCohomology_inr_of_three_le v hr
      exact Subsingleton.elim _ _
  · refine ⟨∑ w : {v : InfinitePlace K.1 // v.IsReal},
      DirectSum.of (localGaloisCohomology K r) (.inl w.1) (f w), ?_⟩
    funext w
    change (∑ w' : {v : InfinitePlace K.1 // v.IsReal},
      DirectSum.of (localGaloisCohomology K r) (.inl w'.1) (f w')) (.inl w.1) = f w
    rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single w]
    · exact DirectSum.of_eq_same _ _
    · intro b _ hb
      exact DirectSum.of_eq_of_ne _ _ _ fun h => hb (Subtype.ext (Sum.inl_injective h)).symm
    · intro h
      exact absurd (Finset.mem_univ w) h

theorem bijective_realLocalization (ι : LocalEmbeddings K) {r : ℕ} (hr : 4 ≤ r) :
    Function.Bijective (realLocalization ι (r := r) (by omega)) :=
  (bijective_realComponents (K := K) (r := r) (by omega)).comp
    ((idelesLimitCohomologyEquiv ι (n := r) (by omega)).bijective.comp
      (bijective_unitsToIdeles_of_four_le hr))

theorem subsingleton_cohomology_unitsLimitRep_of_three_le (hK : ∀ v : InfinitePlace K.1, v.IsComplex)
    {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology (unitsLimitRep K) r) := by
  rcases eq_or_lt_of_le hr with rfl | hr4
  · exact subsingleton_cohomology_three_unitsLimitRep K
  obtain ⟨ι⟩ := nonempty_localEmbeddings K
  have hloc : ∀ v : Place K.1, Subsingleton (localGaloisCohomology K r v) := fun v =>
    subsingleton_localGaloisCohomology_of_not_isReal hr v fun w _ => hK w
  have : Subsingleton (⨁ v : Place K.1, localGaloisCohomology K r v) :=
    ⟨fun a b => DFinsupp.ext fun v => Subsingleton.elim _ _⟩
  have : Subsingleton (cohomology (limitRep K) r) :=
    (idelesLimitCohomologyEquiv ι (n := r) (by omega)).injective.subsingleton
  exact (bijective_unitsToIdeles_of_four_le (K := K) hr4).1.subsingleton

end

end GroundTheory.ProfCoh
