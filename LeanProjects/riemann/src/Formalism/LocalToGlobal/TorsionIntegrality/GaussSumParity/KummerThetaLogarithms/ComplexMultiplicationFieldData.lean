import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementF
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension cW wpNum wpDen uSer)

theorem lubin_tate_log_is_artin_hasse : LtLogIsLgF := by
  intro K _ l hl
  ext n
  unfold Formalism.L2.Th1.CM.ltLog lgF
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have h1 : 1 < l ^ 2 := by nlinarith
  split_ifs with h
  · have hs := Nat.find_spec h
    rw [Finset.sum_eq_single (Nat.find h)]
    · rw [if_pos hs]
    · intro j _ hj
      rw [if_neg]
      intro hj'
      exact hj (Nat.pow_right_injective h1 (hj'.symm.trans hs))
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_range]
      have h2 : Nat.find h < (l ^ 2) ^ Nat.find h := Nat.lt_pow_self h1
      exact Nat.lt_succ_of_lt (lt_of_lt_of_eq h2 hs.symm)
  · symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro hj
    exact h ⟨j, hj⟩

namespace FAux

section Maps

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem cW_eq (g2 g3 : K) (k : ℕ) :
    cW g2 g3 k =
      if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
      if 4 ≤ k then
        3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
          ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
      else 0 := by
  unfold cW
  rw [Nat.strongRecOn_eq]
  split_ifs <;> rfl

theorem cW_map (g2 g3 : K) (k : ℕ) : φ (cW g2 g3 k) = cW (φ g2) (φ g3) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_eq, cW_eq (φ g2) (φ g3) k]
    split_ifs with h2 h3 h4
    · rw [map_div₀, map_ofNat]
    · rw [map_div₀, map_ofNat]
    · rw [map_mul, map_div₀, map_mul, map_add, map_sub, map_mul, map_natCast, map_one, map_sum]
      simp only [map_ofNat]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.isLt
      rw [map_mul, ih (m.val + 2) (by omega), ih (k - (m.val + 2)) (by omega)]
    · exact map_zero φ

theorem wpNum_map (g2 g3 : K) : PowerSeries.map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold wpNum
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs
  · exact map_one φ
  · exact cW_map φ g2 g3 _
  · exact map_zero φ

theorem wpDen_map (g2 g3 : K) : PowerSeries.map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold wpDen
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs
  · exact map_one φ
  · rw [map_mul, map_neg, map_sub, map_natCast, map_one, cW_map]
  · exact map_zero φ

theorem cc_wpDen (g2 g3 : K) : PowerSeries.constantCoeff (wpDen g2 g3) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold wpDen
  rw [PowerSeries.coeff_mk, if_pos rfl]

variable [CharZero K] [CharZero K']

theorem uSer_map (g2 g3 : K) : PowerSeries.map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by
  unfold uSer
  rw [map_mul, map_mul, PowerSeries.map_X,
    Formalism.L2.Th1.B.Map.map_inv' φ (by rw [cc_wpDen]; exact one_ne_zero), wpNum_map, wpDen_map]

theorem cc_arg {l : ℕ} (hl : 2 ≤ l) (ε : K) :
    PowerSeries.constantCoeff (PowerSeries.C ε * lgF K l) = 0 := by
  rw [map_mul, Pair.cc_lgF hl, mul_zero]

theorem thetaS_map {l : ℕ} (hl : 2 ≤ l) (g2 g3 ε : K) :
    PowerSeries.map φ (thetaS l g2 g3 ε) = thetaS l (φ g2) (φ g3) (φ ε) := by
  unfold thetaS
  rw [Formalism.L2.Th1.B.Map.map_psubst' φ (cc_arg hl ε), uSer_map, map_mul, PowerSeries.map_C,
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF]

theorem cc_phFF {l : ℕ} (hl : 2 ≤ l) (g2 g3 s2 ε : K) :
    PowerSeries.constantCoeff (phFF l g2 g3 s2 ε) = 0 := by
  have h1 : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.C ε * lgF K l)
      (Formalism.L2.Th1.B.sigS (Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW g2 g3)))) = 0 :=
    Pair.cc_ps (τ := Unit) (cc_arg hl ε) (Formalism.L2.Th1.B.Map.cc_sigS _)
  have h2 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU (lgF K l) - 1) = 0 := by
    rw [map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hl, sub_self]
  have h3 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU (lgF K l))) = 0 :=
    Pair.cc_ps (τ := Unit) h2 PowerSeries.constantCoeff_log
  unfold phFF
  rw [map_sub, map_add, map_neg, map_mul, map_pow, h1, h3, cc_arg hl ε]
  simp

end Maps

section Field

variable (l : ℕ) [hl : Fact l.Prime]

theorem norm_coe (x : MaximalUnramifiedExtension l) : ‖(MaximalUnramifiedExtension l).subtype x‖ = ‖x‖ := rfl

theorem model (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) (dK : ℕ) (L : PeriodPair)
    (hsq : Squarefree dK) (h4 : dK % 4 = 3) (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (h5 : 5 ≤ l)
    (hd : ¬ l ∣ dK) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (ι : ℂ ≃+* ℂ_[l]) :
    ∃ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
      (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) := by
  obtain ⟨g2, g3, hg⟩ := h2 dK L hsq h4 hcm l h5 hd ι
  obtain ⟨ε, hε, hε1, hc⟩ := h3 dK L hsq h4 hcm l h5 hd hin ι g2 g3 hg
  refine ⟨⟨g2, hg.1⟩, ⟨g3, hg.2.1⟩, ⟨ε, hε⟩, hg, hε1, fun n => ?_⟩
  have hm := thetaS_map (MaximalUnramifiedExtension l).subtype (l := l) (by omega) ⟨g2, hg.1⟩ ⟨g3, hg.2.1⟩ ⟨ε, hε⟩
  have hn := (hc n).2
  rw [lubin_tate_log_is_artin_hasse ℂ_[l] l (by omega)] at hn
  rw [← norm_coe, ← PowerSeries.coeff_map, hm]
  exact hn

theorem ffs (hF1 : CurveExponentCoboundaryCocycle) (g2 g3 ε : MaximalUnramifiedExtension l) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1)
    (hε : ‖ε‖ = 1) (hth : ∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1)
    (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (hF : IsLawOfLog l F) (s2 : MaximalUnramifiedExtension l)
    (hN : ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) :
    F1 F (cob F (phFF l g2 g3 s2 ε)) ∧ F2 l σ (cob F (phFF l g2 g3 s2 ε)) ∧
      Simeq (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * phFF l g2 g3 s2 ε)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l)))
          (cob F (phFF l g2 g3 s2 ε))) := by
  have h1 := hF1 (MaximalUnramifiedExtension l) l hσ.1 hσ.2.1 hσ.2.2.1 F hF g2 g3 s2 ε hg2 hg3 hε hth
  have h2 := second_level_of_norm_holds (MaximalUnramifiedExtension l) l σ hσ F hF _ (cc_phFF hσ.1.two_le g2 g3 s2 ε) h1 hN
  exact ⟨h1, h2.1, h2.2.2⟩

theorem exists_root2 : ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  refine kurRoots l (l ^ 2 - 1) (by omega) fun hd => ?_
  have h2 : l ∣ l ^ 2 := dvd_pow_self l two_ne_zero
  have h3 : l ∣ 1 := by
    have := (Nat.dvd_sub h2 hd)
    rwa [Nat.sub_sub_self h1.le] at this
  exact hl.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem exists_pi : ∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l]) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  exact IsAlgClosed.exists_pow_nat_eq _ (by omega)

end Field

end FAux

theorem complex_multiplication_field_data : FieldDataCM := by
  intro l _ h5
  obtain ⟨σ, hσ, -⟩ := kurFrob l (by omega)
  refine ⟨σ, hσ, (Formalism.InvariantFactorPaths.G7.Top.lawExists (MaximalUnramifiedExtension l) l hσ.1 hσ.2.2.1).1, ?_⟩
  intro d _ hd
  have hl2 := hσ.1.two_le
  have hd0 : d ≠ 0 := NeZero.ne d
  have h1 : 1 < l ^ d := Nat.one_lt_pow hd0 hσ.1.one_lt
  obtain ⟨ζ, hζ⟩ := kurRoots l (l ^ d - 1) (by omega) (fun hdv => by
    have h2 : l ∣ l ^ d := dvd_pow_self l hd0
    have h3 : l ∣ 1 := by
      have := (Nat.dvd_sub h2 hdv)
      rwa [Nat.sub_sub_self h1.le] at this
    exact hσ.1.one_lt.ne' (Nat.dvd_one.1 h3))
  obtain ⟨om, oms, h1, h2⟩ := trDualExists (MaximalUnramifiedExtension l) l d σ hσ hd ζ hζ
  exact ⟨ζ, om, oms, hζ, h1, h2⟩

theorem ThmAEntryCM_of (hF1 : CurveExponentCoboundaryCocycle) : ThmAEntryCM := by
  intro h2 h3 dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  refine ⟨g2, g3, ε, hg, hε, hth, ?_⟩
  intro σ hσ F hF s2 hN
  obtain ⟨a1, a2, -⟩ := FAux.ffs l hF1 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 hN
  exact thmAEntryOfF l (MaximalUnramifiedExtension l) σ hσ (MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2

theorem ThmAGaussCM_of (hF1 : CurveExponentCoboundaryCocycle) : ThmAGaussCM := by
  intro h2 h3 dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  refine ⟨g2, g3, ε, hg, hε, hth, ?_⟩
  intro σ hσ F hF s2 hN
  obtain ⟨a1, a2, -⟩ := FAux.ffs l hF1 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 hN
  exact thmAGaussOfF l (MaximalUnramifiedExtension l) σ hσ (MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2

theorem OneLetterGaussCM_of (hF1 : CurveExponentCoboundaryCocycle) : OneLetterGaussCM := by
  intro h2 h3 dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  refine ⟨g2, g3, ε, hg, hε, hth, ?_⟩
  intro σ hσ F hF s2 hN
  obtain ⟨a1, a2, a3⟩ := FAux.ffs l hF1 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 hN
  exact oneLetterGaussOfF l (MaximalUnramifiedExtension l) σ hσ (MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2
    (FAux.exists_root2 l) _ a3

theorem KernelCM_of (hF1 : CurveExponentCoboundaryCocycle) : KernelCM := by
  intro h2 h3 dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  refine ⟨g2, g3, ε, hg, hε, hth, ?_⟩
  intro σ hσ F hF s2 hN ν r0 r1 _ om oms
  obtain ⟨a1, a2, -⟩ := FAux.ffs l hF1 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 hN
  have : CompleteSpace (MaximalUnramifiedExtension l) := kurComplete l
  exact kernelOfF l (MaximalUnramifiedExtension l) σ hσ (FAux.exists_root2 l) F hF _ a1 a2 ℂ_[l] (MaximalUnramifiedExtension l).subtype ν r0 r1
    (FAux.norm_coe l) (FAux.exists_pi l) om oms

end Formalism.L2.Th1.D
