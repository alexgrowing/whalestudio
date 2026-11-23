import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

open Classical

namespace GlobalTheory.ValUnitLevel
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit Formalism.L2.Host GlobalTheory.ValUnit

theorem isUnit_mk_pow {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsMaximal) {a : R} (ha : a ∉ P) (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (P ^ n) a) := by
  obtain ⟨y, i, hi, e⟩ := hP.exists_inv ha
  have hnil : IsNilpotent (Ideal.Quotient.mk (P ^ n) i) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi n⟩
  have h1 : Ideal.Quotient.mk (P ^ n) y * Ideal.Quotient.mk (P ^ n) a = 1 - Ideal.Quotient.mk (P ^ n) i := by
    rw [← map_mul, eq_sub_iff_add_eq, ← map_add, e, map_one]
  exact isUnit_of_mul_isUnit_right (h1 ▸ hnil.isUnit_one_sub)

theorem exists_pow_sub_one_mem_pow {L : Type} [Field L] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 L))) (a : 𝓞 L)
    (n : HeightOneSpectrum (𝓞 L) → ℕ) (ha : ∀ w ∈ S, a ∉ w.asIdeal) :
    ∃ M : ℕ, 0 < M ∧ ∀ w ∈ S, a ^ M - 1 ∈ w.asIdeal ^ n w := by
  have key : ∀ w ∈ S, ∃ m : ℕ, 0 < m ∧ Ideal.Quotient.mk (w.asIdeal ^ n w) a ^ m = 1 := fun w hw => by
    haveI : Finite (𝓞 L ⧸ w.asIdeal ^ n w) :=
      Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)
    obtain ⟨u, hu⟩ := isUnit_mk_pow w.isMaximal (ha w hw) (n w)
    obtain ⟨m, hm, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite u)
    exact ⟨m, hm, by rw [← hu]; simpa using congrArg Units.val e⟩
  choose! m hm e using key
  refine ⟨∏ w ∈ S, m w, Finset.prod_pos hm, fun w hw => ?_⟩
  rw [← Ideal.Quotient.eq, map_pow, map_one, ← Finset.mul_prod_erase _ _ hw, pow_mul, e w hw, one_pow]

theorem locK_eq_one_of_levelLe {L : Type} [Field L] [NumberField L] {χ : Formalism.L2.Host.HChar L} {w : HeightOneSpectrum (𝓞 L)}
    {n : ℕ} (h : χ.LevelLe w n) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a) (ha0 : a ∉ w.asIdeal)
    (ha : a - 1 ∈ w.asIdeal ^ n) : χ.locK w k = 1 := by
  refine h _ ?_ ?_
  · unfold IsUnitAt
    rw [GlobalTheory.TypeValues.val_atFin w k a hk]
    exact w.intValuation_eq_one_iff.2 ha0
  · have h1 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
        algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (a - 1)) := by
      rw [map_sub, map_sub, map_one, map_one]
      congr 1
      show algebraMap L (w.adicCompletion L) (k : L) = _
      rw [hk]
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (a - 1))) =
        w.valuation L (algebraMap (𝓞 L) L (a - 1)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2, w.valuation_of_algebraMap, w.intValuation_le_pow_iff_mem]
    exact ha

theorem unitOff_val : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (I : Type) [Fintype I]
    (φ : I → L →+* ℂ) (n : I → ℤ) (v : HeightOneSpectrum (𝓞 L)) (q : ℕ), χ.HasInf φ n → χ.UnrAt v →
    (q : 𝓞 L) ∈ v.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff q ((χ.val v : ℂˣ) : ℂ) := by
  intro L _ _ χ I _ φ n v q hinf hv hq
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  choose nl hnl using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · exact ⟨Units.ne_zero _, 1, by simpa using isIntegral_zero, by simpa using isIntegral_zero⟩
  obtain ⟨h, a, hh, ha0, ha⟩ := exists_pow_eq_span v
  have hav : a ∈ v.asIdeal := Ideal.pow_le_self hh.ne' (ha ▸ Ideal.mem_span_singleton_self a)
  have haw : ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → a ∉ w.asIdeal := fun w hw hm => by
    have h1 : v.asIdeal ^ h ≤ w.asIdeal := by rw [ha, Ideal.span_singleton_le_iff_mem]; exact hm
    have h2 : v.asIdeal ≤ w.asIdeal := fun x hx => w.isPrime.mem_of_pow_mem h (h1 (Ideal.pow_mem_pow hx h))
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2).symm)
  obtain ⟨b, hb⟩ : a ∣ (q : 𝓞 L) ^ h := Ideal.mem_span_singleton.1 (ha ▸ Ideal.pow_mem_pow hq h)
  have hvS : v ∉ hfin.toFinset := by simpa using hv
  have hne : ∀ w ∈ hfin.toFinset, w ≠ v := fun w hw e => hvS (e ▸ hw)
  obtain ⟨M, hM, hM1⟩ := exists_pow_sub_one_mem_pow hfin.toFinset a nl fun w hw => haw w (hne w hw)
  have hc0 : a ^ M ≠ 0 := pow_ne_zero _ ha0
  have hk0 : ((a ^ M : 𝓞 L) : L) ≠ 0 := by exact_mod_cast hc0
  set k : Lˣ := Units.mk0 _ hk0 with hk
  have hord : ∀ w : HeightOneSpectrum (𝓞 L), ordF w k = -WithZero.log (w.intValuation (a ^ M)) := fun w => by
    show -WithZero.log (w.valuation L (algebraMap (𝓞 L) L (a ^ M))) = _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
  have hp := GlobalTheory.TypeValues.productRule χ hfin.toFinset (fun w hw => by simpa using hw) k
  rw [Finset.prod_eq_one (fun w hw => locK_eq_one_of_levelLe (hnl w) k (a ^ M) rfl
      (fun hm => haw w (hne w hw) (w.isPrime.mem_of_pow_mem M hm)) (hM1 w hw)), mul_one,
    finprod_eq_single _ v (fun w hw => by
      rw [hord, HeightOneSpectrum.intValuation_eq_one_iff.2 (fun hm => haw w hw (w.isPrime.mem_of_pow_mem M hm))]
      simp), finprod_eq_if, if_pos hvS] at hp
  have hpos : 0 < ordF v k := by
    rw [hord]
    have h0 : v.intValuation (a ^ M) ≠ 0 := v.intValuation_ne_zero _ hc0
    have h3 := (v.intValuation_le_pow_iff_mem (a ^ M) 1).2 (by
      rw [pow_one]; exact Ideal.pow_mem_of_mem _ hav M hM)
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at h3
    push_cast at h3
    omega
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hpos.le
  rw [he, zpow_natCast] at hp
  refine unitOff_of_pow (k := e) (by omega) ?_
  have hp' := congrArg (Units.val : ℂˣ → ℂ) hp
  rw [Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, hinf] at hp'
  rw [eq_inv_of_mul_eq_one_right hp']
  refine unitOff_inv (unitOff_prod _ _ fun i _ => unitOff_zpow (unitOff_div_norm ?_) _)
  have hi : ∀ x : 𝓞 L, IsIntegral ℤ (φ i (algebraMap (𝓞 L) L x)) := fun x =>
    (RingOfIntegers.isIntegral_coe x).map (φ i).toIntAlgHom
  show UnitOff q (φ i (algebraMap (𝓞 L) L (a ^ M)))
  rw [map_pow, map_pow]
  refine unitOff_pow (unitOff_of_mul_eq (m := h) (hi a) (hi b) ?_ hq0.ne') M
  rw [← map_mul, ← map_mul, ← hb, map_pow, map_pow, map_natCast, map_natCast]

end GlobalTheory.ValUnitLevel
