import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingPrimes
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyTransfer
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

theorem gsTateCompactCohomology_eq_zero {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 4 ≤ r) (x : gsTateCompactCohomology S ιr ιs M r) :
    x = 0 :=
  eq_zero_gsTateCompactCohomology_of_coind S ιs ιr
    (fun h2S W _ hr' y => gsTateCompactCohomology_coind_zmodRep_two_eq_zero S ιr h2S ιs W hr' y)
    hr n hn hS M hM x

theorem subsingleton_gsTateCompactCohomology {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 4 ≤ r) :
    Subsingleton (gsTateCompactCohomology S ιr ιs M r) :=
  ⟨fun x y => (gsTateCompactCohomology_eq_zero S ιr ιs hn hS M hM hr x).trans
    (gsTateCompactCohomology_eq_zero S ιr ιs hn hS M hM hr y).symm⟩

set_option maxHeartbeats 4000000 in

theorem injective_gsRealRes_of_four_le {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 4 ≤ r) :
    Function.Injective (gsRealRes S ιr M r).hom := by
  obtain ⟨ιs'⟩ : Nonempty (∀ v : S,
      ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
    ⟨fun _ => Classical.choice nonempty_algHom_of_isSepClosed⟩
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  exact (injective_tateGlobalToLocal_iff (gsFinFamily S ιs') (gsRealFamily S ιr) M
    (fun v => Rep.res (gsFinFamily S ιs' v).toMonoidHom M) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom M) (fun _ => 𝟙 _) (p + 1)
    (fun v => subsingleton_cohomology_gsFinFamily_of_three_le S ιs' hn M hM v (by omega))).1
    (injective_tateGlobalToLocal_of_eq_zero (gsFinFamily S ιs') (gsRealFamily S ιr) M
      (fun v => Rep.res (gsFinFamily S ιs' v).toMonoidHom M) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom M) (fun _ => 𝟙 _) p
      (gsTateCompactCohomology_eq_zero S ιr ιs' hn hS M hM hr))

set_option maxHeartbeats 4000000 in

theorem surjective_gsRealRes_of_three_le {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) :
    Function.Surjective (gsRealRes S ιr M r).hom := by
  obtain ⟨ιs'⟩ : Nonempty (∀ v : S,
      ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
    ⟨fun _ => Classical.choice nonempty_algHom_of_isSepClosed⟩
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  exact (surjective_tateGlobalToLocal_iff (gsFinFamily S ιs') (gsRealFamily S ιr) M
    (fun v => Rep.res (gsFinFamily S ιs' v).toMonoidHom M) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom M) (fun _ => 𝟙 _) (p + 1)
    (fun v => subsingleton_cohomology_gsFinFamily_of_three_le S ιs' hn M hM v (by omega))).1
    (surjective_tateGlobalToLocal_of_eq_zero (gsFinFamily S ιs') (gsRealFamily S ιr) M
      (fun v => Rep.res (gsFinFamily S ιs' v).toMonoidHom M) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom M) (fun _ => 𝟙 _) p
      (gsTateCompactCohomology_eq_zero S ιr ιs' hn hS M hM (by omega)))

end

end GroundTheory.ProfCoh
