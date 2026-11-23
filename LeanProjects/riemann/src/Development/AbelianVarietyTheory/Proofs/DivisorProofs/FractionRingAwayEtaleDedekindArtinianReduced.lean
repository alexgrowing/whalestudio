import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

namespace GlobalTheory

theorem mem_minimalPrimes_of_disjoint_nonZeroDivisors {R : Type} [CommRing R] [IsReduced R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (hp : Disjoint (p : Set R) (nonZeroDivisors R)) :
    p ∈ minimalPrimes R := by
  classical
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  have hsub : (p : Set R) ⊆ ⋃ q ∈ hfin.toFinset, (q : Set R) := by
    intro x hx
    have hx' : x ∉ nonZeroDivisors R := Set.disjoint_left.mp hp hx
    rw [mem_nonZeroDivisors_iff_right] at hx'
    push_neg at hx'
    obtain ⟨y, hxy, hy⟩ := hx'
    have hrad : (⊥ : Ideal R).radical = ⊥ := by
      exact nilradical_eq_zero R
    have : x ∈ ⋃ q ∈ (⊥ : Ideal R).minimalPrimes, (q : Set R) := by
      rw [Ideal.iUnion_minimalPrimes]
      refine ⟨y, ?_, ?_⟩
      · rw [hrad]; simpa using hy
      · rw [hrad]; simpa [mul_comm] using hxy
    simpa [Set.Finite.mem_toFinset] using this
  have hprime : ∀ q ∈ hfin.toFinset, q.IsPrime := fun q hq =>
    ((Set.Finite.mem_toFinset hfin).1 hq).isPrime
  obtain ⟨q, hq, hpq⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) ⊥ fun q hq _ _ => hprime q hq).1 hsub
  have hqm : q ∈ minimalPrimes R := (Set.Finite.mem_toFinset hfin).1 hq
  have : q ≤ p := hqm.2 ⟨inferInstance, bot_le⟩ hpq
  exact (le_antisymm hpq this) ▸ hqm

theorem total_fractions_isArtinian_isReduced (R : Type) [CommRing R] [IsReduced R]
    [IsNoetherianRing R] : IsArtinianRing (FractionRing R) ∧ IsReduced (FractionRing R) := by
  have hN : IsNoetherianRing (FractionRing R) :=
    IsLocalization.isNoetherianRing (nonZeroDivisors R) _ inferInstance
  have hRed : IsReduced (FractionRing R) := inferInstance
  refine ⟨?_, hRed⟩
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  refine ⟨hN, Ring.krullDimLE_zero_iff.mpr fun P hP => ?_⟩
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
  have key : ∀ (Q : Ideal (FractionRing R)), Q.IsPrime →
      Q.comap (algebraMap R (FractionRing R)) ∈ minimalPrimes R := by
    intro Q hQ
    have h := (IsLocalization.isPrime_iff_isPrime_disjoint (nonZeroDivisors R) (FractionRing R) Q).1 hQ
    haveI := h.1
    exact mem_minimalPrimes_of_disjoint_nonZeroDivisors _ h.2.symm
  have h1 := key P hP
  have h2 := key M hM.isPrime
  have hle : M.comap (algebraMap R (FractionRing R)) ≤ P.comap (algebraMap R (FractionRing R)) :=
    h2.2 ⟨h1.1.1, bot_le⟩ (Ideal.comap_mono hPM)
  have : P = M := by
    rw [← IsLocalization.map_comap (nonZeroDivisors R) (FractionRing R) P,
      ← IsLocalization.map_comap (nonZeroDivisors R) (FractionRing R) M]
    exact congrArg _ (le_antisymm (Ideal.comap_mono hPM) hle)
  exact this ▸ hM

theorem fractionRing_away_etale_isArtinian_isReduced : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsArtinianRing (FractionRing (Localization.Away (algebraMap B A' f))) ∧ IsReduced (FractionRing (Localization.Away (algebraMap B A' f))) := by
  intro B _ _ f A' _ _ _
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing B A'
  have : IsReduced A' := GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing B A'
  have : IsNoetherianRing (Localization.Away (algebraMap B A' f)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (algebraMap B A' f)) _ inferInstance
  have : IsReduced (Localization.Away (algebraMap B A' f)) := inferInstance
  exact total_fractions_isArtinian_isReduced _

end GlobalTheory
