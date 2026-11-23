import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLengthParameters
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRegularElement
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthLocalizedQuotient
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

theorem mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq (hCM : CMRegularElement.Statement.{u})
    {B : Type u} [CommRing B] [IsCohenMacaulayLocalRing B] {P : Ideal B} (hmin : minimalPrimes B = {P})
    {s : B} (hs : s ∉ P) : s ∈ nonZeroDivisors B := by
  by_cases hsm : s ∈ maximalIdeal B
  · refine (hCM B s hsm fun p hp => ?_).1
    rw [hmin, Set.mem_singleton_iff] at hp
    rwa [hp]
  · exact ((IsLocalRing.notMem_maximalIdeal.1 hsm)).mem_nonZeroDivisors

theorem length_localization_maximalIdeal (B : Type u) [CommRing B] [IsLocalRing B] :
    Module.length (Localization.AtPrime (maximalIdeal B)) (Localization.AtPrime (maximalIdeal B)) =
      Module.length B B := by
  have hU : (maximalIdeal B).primeCompl ≤ IsUnit.submonoid B := fun s hs =>
    IsLocalRing.notMem_maximalIdeal.1 hs
  let e := IsLocalization.atUnits B (maximalIdeal B).primeCompl
    (S := Localization.AtPrime (maximalIdeal B)) hU
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime (maximalIdeal B))) :=
    e.surjective
  rw [← Module.length_eq_of_surjective (S := B) hsurj]
  exact e.toLinearEquiv.length_eq.symm

theorem withBot_natCast_le_of_add_one_le {k : ℕ} {D : WithBot ℕ∞}
    (h : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ D + 1) : ((k : ℕ) : WithBot ℕ∞) ≤ D := by
  induction D using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe n =>
      have h' : k + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : k ≤ n)

theorem spanFinrank_span_range_le {R : Type*} [CommRing R] {k : ℕ} (z : Fin k → R) :
    (Ideal.span (Set.range z)).spanFinrank ≤ k := by
  classical
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
  have hz : Set.range z = ((Finset.univ.image z : Finset R) : Set R) := by simp
  rw [hz, Set.ncard_coe_finset]
  exact Finset.card_image_le.trans (by simp)

theorem span_range_eq_span_range_succ {R : Type*} [CommRing R] {k : ℕ} (z : Fin (k + 1) → R) (h0 : z 0 = 0) :
    Ideal.span (Set.range z) = Ideal.span (Set.range fun j : Fin k => z j.succ) := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono ?_)
  · rintro _ ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => rw [h0]; exact Ideal.zero_mem _
    | succ j => exact Ideal.subset_span ⟨j, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.succ, rfl⟩

theorem maximalIdeal_quotient_eq_span {B : Type u} [CommRing B] [IsLocalRing B] {I : Ideal B} {k : ℕ}
    (x : Fin k → B) (hI : Ideal.span (Set.range x) ⊔ I = maximalIdeal B) [IsLocalRing (B ⧸ I)] :
    maximalIdeal (B ⧸ I) = Ideal.span (Set.range fun i => Ideal.Quotient.mk I (x i)) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, ← hI, Ideal.map_sup,
    Ideal.map_span, ← Set.range_comp, Ideal.map_quotient_self, sup_bot_eq]
  rfl

theorem notMem_and_isPrime_sup_span {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {P : Ideal B} [hP : P.IsPrime] {k : ℕ} (x : Fin (k + 1) → B)
    (hdim : ringKrullDim (B ⧸ P) = ((k + 1 : ℕ) : WithBot ℕ∞))
    (hmax : Ideal.span (Set.range x) ⊔ P = maximalIdeal B) :
    x 0 ∉ P ∧ (P ⊔ Ideal.span {x 0}).IsPrime ∧
      ringKrullDim (B ⧸ (P ⊔ Ideal.span {x 0})) = ((k : ℕ) : WithBot ℕ∞) := by
  have hPm : P ≤ maximalIdeal B := hmax ▸ le_sup_right
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  have : Nontrivial (B ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have : IsLocalRing (B ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hA := maximalIdeal_quotient_eq_span x hmax
  have hy : x 0 ∉ P := by
    intro hyP
    have h0 : Ideal.Quotient.mk P (x 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hyP
    have hle := ringKrullDim_le_spanFinrank_maximalIdeal (B ⧸ P)
    rw [hA, span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk P (x i)) h0, hdim] at hle
    have hk := spanFinrank_span_range_le (fun j : Fin k => Ideal.Quotient.mk P (x j.succ))
    have h2 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞) := hle.trans (by exact_mod_cast hk)
    have h3 : k + 1 ≤ k := by exact_mod_cast h2
    omega
  set Q₀ := P ⊔ Ideal.span {x 0} with hQ₀
  have hQ₀m : Q₀ ≤ maximalIdeal B := sup_le hPm ((Ideal.span_singleton_le_iff_mem _).2 (hxm 0))
  have hmaxQ : Ideal.span (Set.range x) ⊔ Q₀ = maximalIdeal B :=
    le_antisymm (sup_le (hmax ▸ le_sup_left) hQ₀m) (hmax ▸ sup_le_sup_left le_sup_left _)
  have : Nontrivial (B ⧸ Q₀) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hQ₀m))
  have : IsLocalRing (B ⧸ Q₀) := IsLocalRing.of_surjective' (Ideal.Quotient.mk Q₀) Ideal.Quotient.mk_surjective
  have hA' := maximalIdeal_quotient_eq_span x hmaxQ
  have h0' : Ideal.Quotient.mk Q₀ (x 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk Q₀ (x i)) h0'] at hA'
  have hfin : (maximalIdeal (B ⧸ Q₀)).spanFinrank ≤ k := hA' ▸ spanFinrank_span_range_le _
  have hge : ((k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Q₀) := by
    have e : (B ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P (x 0)} ≃+* B ⧸ Q₀ :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup P (Ideal.span {x 0}))
    have hj : ({Ideal.Quotient.mk P (x 0)} : Set (B ⧸ P)) ⊆ Ring.jacobson (B ⧸ P) := by
      rw [Set.singleton_subset_iff, IsLocalRing.ringJacobson_eq_maximalIdeal, hA]
      exact Ideal.subset_span ⟨0, rfl⟩
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard _ hj
    rw [hdim, Set.encard_singleton, ringKrullDim_eq_of_ringEquiv e] at h
    exact withBot_natCast_le_of_add_one_le (by exact_mod_cast h)
  have hle : ringKrullDim (B ⧸ Q₀) ≤ ((k : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans (by exact_mod_cast hfin)
  have : IsRegularLocalRing (B ⧸ Q₀) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ((by exact_mod_cast hfin :
      ((maximalIdeal (B ⧸ Q₀)).spanFinrank : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞)).trans hge)
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := B ⧸ Q₀)
  exact ⟨hy, (Ideal.Quotient.isDomain_iff_prime Q₀).1 inferInstance, le_antisymm hle hge⟩

theorem CMLengthParameters.proof (hCM : CMRegularElement.Statement.{u})
    (hLen : LengthLocalizedQuotient.Statement.{u}) : CMLengthParameters.Statement.{u} := by
  suffices h : ∀ d : ℕ, ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime]
      (x : Fin d → B), minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
      Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
        Module.length B (B ⧸ Ideal.span (Set.range x)) =
          Module.length (Localization.AtPrime P) (Localization.AtPrime P) from
    fun B _ _ P _ d x => h d B P x
  intro d
  induction d with
  | zero =>
    intro B _ _ P _ x _ _ hmax
    have hx : Ideal.span (Set.range x) = ⊥ := by rw [Set.range_eq_empty, Ideal.span_empty]
    rw [hx, bot_sup_eq] at hmax
    subst hmax
    rw [hx, length_localization_maximalIdeal]
    exact (Submodule.quotEquivOfEqBot ⊥ rfl).length_eq
  | succ k ih =>
    intro B _ _ P _ x hmin hdim hmax
    obtain ⟨hyP, hQ₀, hdimQ⟩ := notMem_and_isPrime_sup_span x hdim hmax
    set y := x 0 with hy
    set Q₀ := P ⊔ Ideal.span {y} with hQ₀def
    have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
    have hnzd : ∀ s ∉ P, s ∈ nonZeroDivisors B := fun s hs =>
      mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq hCM hmin hs
    have hyQ : Ideal.span {y} ≤ Q₀ := le_sup_right

    have hB'CM : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y}) := (hCM B y (hxm 0) fun p hp => by
      rw [hmin, Set.mem_singleton_iff] at hp
      rwa [hp]).2
    set f := Ideal.Quotient.mk (Ideal.span {y}) with hf
    have hfs : Function.Surjective f := Ideal.Quotient.mk_surjective
    have hker : RingHom.ker f ≤ Q₀ := by rw [hf, Ideal.mk_ker]; exact hyQ
    set P' := Q₀.map f with hP'def
    have hP' : P'.IsPrime := Ideal.map_isPrime_of_surjective hfs hker
    have hcomap : P'.comap f = Q₀ := by
      rw [hP'def, Ideal.comap_map_of_surjective' f hfs, sup_eq_left.2 hker]

    have hall : ∀ q : Ideal (B ⧸ Ideal.span {y}), q.IsPrime → P' ≤ q := by
      intro q hq
      have hqc : (q.comap f).IsPrime := Ideal.comap_isPrime f q
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q.comap f)
      have hpP : p = P := by
        have : p ∈ minimalPrimes B := hp
        rw [hmin, Set.mem_singleton_iff] at this
        exact this
      subst hpP
      have hyq : Ideal.span {y} ≤ q.comap f := fun z hz => by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hz]
        exact q.zero_mem
      rw [hP'def, Ideal.map_le_iff_le_comap]
      exact sup_le hpq hyq
    have hmin' : minimalPrimes (B ⧸ Ideal.span {y}) = {P'} := by
      ext q
      rw [Set.mem_singleton_iff]
      constructor
      · intro hq
        exact le_antisymm (hq.2 ⟨hP', bot_le⟩ (hall q hq.1.1)) (hall q hq.1.1)
      · rintro rfl
        exact ⟨⟨hP', bot_le⟩, fun q hq _ => hall q hq.1⟩
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {y}) ⧸ P') = (k : ℕ) := by
      rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hyQ)]
      exact hdimQ

    set x' : Fin k → B ⧸ Ideal.span {y} := fun j => f (x j.succ) with hx'
    have hmB' : (maximalIdeal B).map f = maximalIdeal (B ⧸ Ideal.span {y}) :=
      map_maximalIdeal_of_surjective f hfs
    have hmax' : Ideal.span (Set.range x') ⊔ P' = maximalIdeal (B ⧸ Ideal.span {y}) := by
      apply le_antisymm
      · refine sup_le (Ideal.span_le.2 ?_) (IsLocalRing.le_maximalIdeal hP'.ne_top)
        rintro _ ⟨j, rfl⟩
        rw [← hmB']
        exact Ideal.mem_map_of_mem f (hxm _)
      · rw [← hmB', Ideal.map_le_iff_le_comap, ← hmax]
        refine sup_le (Ideal.span_le.2 ?_) fun p hp => ?_
        · rintro _ ⟨i, rfl⟩
          cases i using Fin.cases with
          | zero =>
            exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
          | succ j => exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
        · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_left hp))
    have key := ih (B ⧸ Ideal.span {y}) P' x' hmin' hdim' hmax'
    rw [hLen B P y hmin hnzd hyP P' hcomap] at key
    rw [← key]

    have hyx : Ideal.span {y} ≤ Ideal.span (Set.range x) :=
      (Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span ⟨0, rfl⟩)
    have hJ : (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y})) = Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      refine span_range_eq_span_range_succ _ ?_
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    calc Module.length B (B ⧸ Ideal.span (Set.range x))
        = Module.length B ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          (DoubleQuot.quotQuotEquivQuotOfLEₐ B hyx).toLinearEquiv.length_eq.symm
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸ Ideal.span (Set.range x')) := by
          rw [hJ]

end GroundTheory.Heights₂.Heights
