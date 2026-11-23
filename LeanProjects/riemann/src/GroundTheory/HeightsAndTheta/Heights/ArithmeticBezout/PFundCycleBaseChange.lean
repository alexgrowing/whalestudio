import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFundCycleBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMinimalPrimeComap
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem localMult_map_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (J W : Ideal A) [W.IsPrime] (W' : Ideal B) [W'.IsPrime] [W'.LiesOver W]
    (hfib : (W.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) =
      IsLocalRing.maximalIdeal (Localization.AtPrime W')) :
    localMult (J.map (algebraMap A B)) W' = localMult J W := by
  let := Localization.AtPrime.algebraOfLiesOver W W'
  have : IsLocalHom (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have htow : (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')).comp
      (algebraMap A (Localization.AtPrime W)) =
      (algebraMap B (Localization.AtPrime W')).comp (algebraMap A B) := by
    ext x
    exact Localization.localRingHom_to_map _ _ _ Ideal.LiesOver.over x
  have hmap : ∀ I : Ideal A, (I.map (algebraMap A (Localization.AtPrime W))).map
      (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) =
      (I.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) := by
    intro I
    rw [Ideal.map_map, Ideal.map_map, htow]
  have key := IsLocalRing.length_baseChange (Localization.AtPrime W) (Localization.AtPrime W')
    (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W')
    (J.map (algebraMap A (Localization.AtPrime W)))).toLinearEquiv.length_eq, hmap,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), hmap, hfib] at key
  have : IsSimpleModule (Localization.AtPrime W')
      (Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one (R := Localization.AtPrime W')
    (M := Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')), mul_one] at key
  unfold localMult
  rw [dif_pos ‹W'.IsPrime›, dif_pos ‹W.IsPrime›, key]

section MinimalPrimes

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
  (hc : ∀ I : Ideal A, I.IsPrime → ∀ P ∈ (I.map f).minimalPrimes, P.comap f = I)
include hc

theorem comap_mem_minimalPrimes {J : Ideal A} {P : Ideal B} (hP : P ∈ (J.map f).minimalPrimes) :
    P.comap f ∈ J.minimalPrimes ∧ P ∈ ((P.comap f).map f).minimalPrimes := by
  have hPp : P.IsPrime := hP.1.1
  obtain ⟨W₀, hW₀, hW₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hP.1.2)
  have hW₀p : W₀.IsPrime := hW₀.1.1
  obtain ⟨P₀, hP₀, hP₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mpr hW₀le)
  have hP₀p : P₀.IsPrime := hP₀.1.1
  have hEq : P₀ = P :=
    le_antisymm hP₀le (hP.2 ⟨hP₀p, (Ideal.map_mono hW₀.1.2).trans hP₀.1.2⟩ hP₀le)
  subst hEq
  rw [hc W₀ hW₀p P₀ hP₀]
  exact ⟨hW₀, hP₀⟩

theorem mem_minimalPrimes_map {J W : Ideal A} (hW : W ∈ J.minimalPrimes) {P : Ideal B}
    (hP : P ∈ (W.map f).minimalPrimes) : P ∈ (J.map f).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.1.1
  refine ⟨⟨hPp, (Ideal.map_mono hW.1.2).trans hP.1.2⟩, fun Q hQ hQP => ?_⟩
  have hQp : Q.IsPrime := hQ.1
  obtain ⟨Q₀, hQ₀, hQ₀le⟩ := Ideal.exists_minimalPrimes_le hQ.2
  obtain ⟨h1, -⟩ := comap_mem_minimalPrimes f hc hQ₀
  have hle : Q₀.comap f ≤ W := by
    rw [← hc W hWp P hP]
    exact Ideal.comap_mono (hQ₀le.trans hQP)
  have hWQ : W ≤ Q₀.comap f := hW.2 h1.1 hle
  have hQ₀p : Q₀.IsPrime := hQ₀.1.1
  exact (hP.2 ⟨hQ₀p, Ideal.map_le_iff_le_comap.mpr hWQ⟩ (hQ₀le.trans hQP)).trans hQ₀le

end MinimalPrimes

theorem isRelevant_comap_map_iff {K L : Type*} [CommRing K] [CommRing L] (σ : K →+* L) {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) L)) :
    IsRelevant (P.comap (MvPolynomial.map σ)) ↔ IsRelevant P := by
  simp [IsRelevant, Ideal.mem_comap, MvPolynomial.map_X]

theorem fundCycle_apply {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (J W : Ideal (MvPolynomial (Fin n) R)) [Decidable (W ∈ relComps J)] :
    fundCycle J W = if W ∈ relComps J then localMult J W else 0 := by
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  congr

theorem FundCycleBaseChange.proof (h : MinimalPrimeComap.Statement) : FundCycleBaseChange.Statement := by
  classical
  intro K L _ _ _ σ n J
  have hc : ∀ I : Ideal (MvPolynomial (Fin n) K), I.IsPrime →
      ∀ P ∈ (I.map (MvPolynomial.map σ)).minimalPrimes, P.comap (MvPolynomial.map σ) = I :=
    fun I hI P hP => h K L σ (Fin n) I hI P hP
  have hrad := RadicalBaseChange.proof
  let := σ.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := K) (S := L)
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange (R := K) (S := MvPolynomial (Fin n) K) (M := L)
      (N := MvPolynomial (Fin n) L) (h := Algebra.IsPushout.out (R := K) (S := MvPolynomial (Fin n) K) (R' := L)
        (S' := MvPolynomial (Fin n) L))
  have hsupp : ∀ W ∈ (fundCycle J).support, W ∈ relComps J := by
    intro W hW
    by_contra hn
    exact Finsupp.mem_support_iff.mp hW (by rw [fundCycle_apply, if_neg hn])
  have hone : ∀ W : Ideal (MvPolynomial (Fin n) K), W.IsPrime → ∀ P,
      P ∈ relComps (W.map (MvPolynomial.map σ)) → localMult (W.map (MvPolynomial.map σ)) P = 1 :=
    fun W hW P hP => localMult_eq_one_of_isRadical (hrad K L σ (Fin n) W hW.isRadical) hP.1
  ext P
  rw [Finsupp.finsetSum_apply, fundCycle_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  split_ifs with hP
  · obtain ⟨hWmin, hPW⟩ := comap_mem_minimalPrimes _ hc hP.1
    have hWrel : P.comap (MvPolynomial.map σ) ∈ relComps J :=
      ⟨hWmin, (isRelevant_comap_map_iff σ P).mpr hP.2⟩
    have hWp : (P.comap (MvPolynomial.map σ)).IsPrime := hWmin.1.1
    have hPp : P.IsPrime := hP.1.1.1
    have : P.LiesOver (P.comap (MvPolynomial.map σ)) := ⟨rfl⟩
    have hmult : localMult (J.map (MvPolynomial.map σ)) P =
        localMult J (P.comap (MvPolynomial.map σ)) :=
      localMult_map_of_flat J _ P (map_eq_maximalIdeal_of_isRadical
        (hrad K L σ (Fin n) _ hWp.isRadical) hPW)
    rw [hmult, Finset.sum_eq_single (P.comap (MvPolynomial.map σ))]
    · rw [fundCycle_apply J, if_pos hWrel,
        fundCycle_apply (Ideal.map (MvPolynomial.map σ) (P.comap (MvPolynomial.map σ))) P,
        if_pos ⟨hPW, hP.2⟩, hone _ hWp P ⟨hPW, hP.2⟩, mul_one]
    · intro W₀ hW₀ hne
      rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W₀) P, if_neg, mul_zero]
      intro hPW₀
      exact hne (hc W₀ (hsupp W₀ hW₀).1.1.1 P hPW₀.1).symm
    · intro hW
      rw [Finsupp.notMem_support_iff.mp hW, zero_mul]
  · refine (Finset.sum_eq_zero fun W hW => ?_).symm
    rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W) P, if_neg, mul_zero]
    intro hPW
    exact hP ⟨mem_minimalPrimes_map _ hc (hsupp W hW).1 hPW.1, hPW.2⟩

end GroundTheory.Heights₂.Heights
