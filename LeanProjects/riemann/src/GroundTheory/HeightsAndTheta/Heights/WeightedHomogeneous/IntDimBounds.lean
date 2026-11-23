import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IntDimTrdeg

set_option linter.style.haveILetI false

namespace GroundTheory.Heights₂.Heights

open Algebra Cardinal
open scoped TensorProduct

noncomputable section

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hb : P = ⊥
  · subst hb
    refine le_antisymm (fun n hn => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at hn
    have h := hn n
    rw [Int.isUnit_iff] at h
    rw [Ideal.mem_bot]
    rcases h with h | h
    · exact mul_self_eq_zero.mp (by linarith)
    · nlinarith [mul_self_nonneg n]
  · haveI := hP
    haveI : P.IsMaximal := IsPrime.to_maximal_ideal hb
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem ringKrullDim_le_add_one_of_quotient_le {B : Type} [CommRing B] [IsDomain B] (n : ℕ∞)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q ≠ ⊥ → ringKrullDim (B ⧸ Q) ≤ n) :
    ringKrullDim B ≤ ((n + 1 : ℕ∞) : WithBot ℕ∞) := by
  let P0 : PrimeSpectrum B := ⟨⊥, Ideal.isPrime_bot⟩
  have hco : Order.coheight P0 ≤ n + 1 := by
    rw [Order.coheight_eq_iSup_gt_coheight]
    refine iSup₂_le fun Q hQ => ?_
    have hQ0 : Q.asIdeal ≠ ⊥ := by
      intro h0
      have : Q = P0 := PrimeSpectrum.ext h0
      rw [this] at hQ
      exact lt_irrefl _ hQ
    have h1 := h Q.asIdeal Q.isPrime hQ0
    rw [← GroundTheory.Arith.Abelian.Jacobian.coheight_eq_ringKrullDim_quotient] at h1
    have h2 : Order.coheight Q ≤ n := by exact_mod_cast h1
    exact add_le_add h2 le_rfl
  show Order.krullDim (PrimeSpectrum B) ≤ _
  rw [Order.krullDim_eq_iSup_coheight_of_nonempty]
  refine WithBot.coe_le_coe.mpr (iSup_le fun Q => ?_)
  have hle : P0 ≤ Q := by
    change (⊥ : Ideal B) ≤ Q.asIdeal
    exact bot_le
  exact (Order.coheight_anti hle).trans hco

theorem ringKrullDim_le_trdeg_add_one_int (t : ℕ) : ∀ (B : Type) [CommRing B] [IsDomain B]
    [Algebra ℤ B] [Algebra.FiniteType ℤ B], Function.Injective (algebraMap ℤ B) →
    trdeg ℤ B = t → ringKrullDim B ≤ (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro B _ _ _ _ hinj ht
  have hfin : trdeg ℤ B < ℵ₀ := by rw [ht]; exact Cardinal.natCast_lt_aleph0
  have key := ringKrullDim_le_add_one_of_quotient_le (B := B) (t : ℕ∞) (fun Q hQ hQ0 => by
    haveI := hQ
    haveI : Algebra.FiniteType ℤ (B ⧸ Q) :=
      .of_surjective (Ideal.Quotient.mkₐ ℤ Q) (Ideal.Quotient.mkₐ_surjective ℤ Q)
    by_cases hc : Function.Injective (algebraMap ℤ (B ⧸ Q))
    · have hlt := trdeg_lt_of_surjective_of_ker_ne_bot (Ideal.Quotient.mkₐ ℤ Q)
        (Ideal.Quotient.mkₐ_surjective ℤ Q)
        (fun h => hQ0 (by rw [← Ideal.mk_ker (I := Q)]; exact h)) hc hfin
      obtain ⟨t', ht'⟩ := Cardinal.lt_aleph0.mp (hlt.trans hfin)
      rw [ht, ht'] at hlt
      have hlt' : t' < t := by exact_mod_cast hlt
      refine (ih t' hlt' (B ⧸ Q) hc ht').trans ?_
      exact_mod_cast (show t' + 1 ≤ t by omega)
    · have hp0 : ringChar (B ⧸ Q) ≠ 0 := by
        intro h0
        have hc0 := ringChar.charP (B ⧸ Q)
        rw [h0] at hc0
        haveI : CharZero (B ⧸ Q) := (CharP.charP_zero_iff_charZero _).mp hc0
        apply hc
        have e : algebraMap ℤ (B ⧸ Q) = Int.castRingHom (B ⧸ Q) := RingHom.ext_int _ _
        rw [e]
        exact Int.cast_injective
      haveI : CharP (B ⧸ Q) (ringChar (B ⧸ Q)) := ringChar.charP _
      have hpp : (ringChar (B ⧸ Q)).Prime :=
        (CharP.char_is_prime_or_zero (B ⧸ Q) (ringChar (B ⧸ Q))).resolve_right hp0
      haveI : Fact (ringChar (B ⧸ Q)).Prime := ⟨hpp⟩
      letI := ZMod.algebra (B ⧸ Q) (ringChar (B ⧸ Q))
      haveI := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (B ⧸ Q))
        ((algebraMap (ZMod (ringChar (B ⧸ Q))) (B ⧸ Q)).comp (algebraMap ℤ (ZMod (ringChar (B ⧸ Q))))))
      haveI : Algebra.FiniteType (ZMod (ringChar (B ⧸ Q))) (B ⧸ Q) :=
        Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
      have hle := trdeg_zmod_quotient_le hinj (ringChar (B ⧸ Q)) Q
      rw [ht] at hle
      obtain ⟨s, hs⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt Cardinal.natCast_lt_aleph0)
      rw [hs] at hle
      have hst : s ≤ t := by exact_mod_cast hle
      rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg (ZMod (ringChar (B ⧸ Q))), hs,
        Cardinal.toENat_nat]
      exact_mod_cast hst)
  refine key.trans (le_of_eq ?_)
  push_cast
  rfl

theorem le_ringKrullDim_int (B : Type) [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B]
    (hinj : Function.Injective (algebraMap ℤ B)) (t : ℕ) (ht : trdeg ℤ B = t) :
    (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim B := by
  letI : Algebra B (ℚ ⊗[ℤ] B) := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨n, hn, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    exact nonZeroDivisors.ne_zero hn (hinj (h.trans (map_zero _).symm))
  haveI : IsLocalization M (ℚ ⊗[ℤ] B) := IsLocalization.tensorRight _ _
  haveI : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM

  have hBL : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B)) := IsLocalization.injective _ hM
  haveI : FaithfulSMul B (ℚ ⊗[ℤ] B) := (faithfulSMul_iff_algebraMap_injective _ _).2 hBL
  haveI : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : FaithfulSMul ℤ ℚ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℤ ℚ).injective_int
  haveI : FaithfulSMul ℚ (ℚ ⊗[ℤ] B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℚ (ℚ ⊗[ℤ] B)).injective
  haveI := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap B (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ B)))
  haveI := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap ℚ (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ ℚ)))
  haveI : Algebra.IsAlgebraic B (ℚ ⊗[ℤ] B) := IsLocalization.isAlgebraic _ M
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have h1 := trdeg_add_eq ℤ B (A := ℚ ⊗[ℤ] B)
  have h2 := trdeg_add_eq ℤ ℚ (A := ℚ ⊗[ℤ] B)
  rw [trdeg_eq_zero (R := B) (A := ℚ ⊗[ℤ] B), add_zero] at h1
  rw [trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add] at h2
  have htL : trdeg ℚ (ℚ ⊗[ℤ] B) = t := by rw [h2, ← h1, ht]

  obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℚ ⊗[ℤ] B)
  have hmh : m.height = t := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field (K := ℚ) t htL m
  have hPh : (m.under B).height = t := (IsLocalization.height_under M m).trans hmh
  have hdisj : Disjoint (M : Set B) (m.under B) :=
    (IsLocalization.disjoint_under_iff M _ m).2 hm.ne_top
  have hnm : ¬ (m.under B).IsMaximal := by
    intro hPm
    letI := Ideal.Quotient.field (m.under B)
    haveI : IsJacobsonRing ℤ := isJacobsonRing_int
    haveI : Algebra.FiniteType ℤ (B ⧸ m.under B) :=
      .of_surjective (Ideal.Quotient.mkₐ ℤ _) (Ideal.Quotient.mkₐ_surjective ℤ _)
    haveI := finite_of_finite_type_of_isJacobsonRing ℤ (B ⧸ m.under B)
    haveI : Algebra.IsIntegral ℤ (B ⧸ m.under B) := Algebra.IsIntegral.of_finite ℤ _
    apply Int.not_isField
    refine isField_of_isIntegral_of_isField ?_ (Field.toIsField (B ⧸ m.under B))
    have e : algebraMap ℤ (B ⧸ m.under B) = (Ideal.Quotient.mk _).comp (algebraMap ℤ B) :=
      RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    by_contra hn0
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hn
    exact Set.disjoint_left.mp hdisj ⟨n, mem_nonZeroDivisors_of_ne_zero hn0, rfl⟩ hn
  obtain ⟨N, hN, hPN⟩ := (m.under B).exists_le_maximal (Ideal.IsPrime.ne_top inferInstance)
  have hlt : m.under B < N := lt_of_le_of_ne hPN (fun h => hnm (h ▸ hN))
  have hh := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hPh] at hh
  calc (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (N.height : WithBot ℕ∞) := by
        exact_mod_cast hh
    _ ≤ ringKrullDim B := Ideal.height_le_ringKrullDim_of_isPrime

end

end GroundTheory.Heights₂.Heights
