import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.MassRatioInvBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma sqrt_pow_eq_pow_sqrt (a : ℝ) (ha : 0 ≤ a) (f : ℕ) : Real.sqrt (a ^ f) = Real.sqrt a ^ f := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) f), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt ha]

private lemma one_le_factorial_mul_exp_div_pow (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ ((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk0 : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkpos k
  have hn : (k - 1).factorial * k = k.factorial := by
    rw [mul_comm]; exact Nat.mul_factorial_pred (by omega)
  have hf : ((k - 1).factorial : ℝ) * k = (k.factorial : ℝ) := by exact_mod_cast hn
  rw [hf, le_div_iff₀ hk0, one_mul, Real.exp_one_pow]
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (Nat.cast_nonneg k) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hfac] at h
  rw [mul_comm]
  exact h

theorem one_le_ratio_mul (f k : ℕ) (v L : ℝ) (hv : 0 < v) (hk : 1 ≤ k) (hL : ((2 : ℝ) ^ f)⁻¹ ≤ L) :
    1 ≤ (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt ((2 * v) ^ f) * L *
      ((Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (2 * (k : ℝ) * (2 * v) ^ ((1 : ℝ) / 2)) ^ f) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpi := Real.pi_pos
  have hs0 : 0 < Real.sqrt (2 * v) := Real.sqrt_pos.mpr (by linarith)
  have hrp : (2 * v) ^ ((1 : ℝ) / 2) = Real.sqrt (2 * v) := by rw [Real.sqrt_eq_rpow]
  rw [hrp, sqrt_pow_eq_pow_sqrt (2 * v) (by linarith) f, pow_mul]

  have hcol : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt (2 * v) ^ f * L *
      (((Real.exp 1 * Real.pi / (k * v)) ^ k) ^ f * (2 * (k : ℝ) * Real.sqrt (2 * v)) ^ f) =
      ((((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
        (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v)) ^ f * L := by
    rw [div_pow, mul_pow, mul_pow]
    ring

  have hbase : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
      (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v) =
      (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) * 2 := by
    have hv0 : v ≠ 0 := hv.ne'
    have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
    have hp0 : Real.pi ≠ 0 := hpi.ne'
    have hs : Real.sqrt (2 * v) ≠ 0 := hs0.ne'
    rw [div_pow, div_pow, mul_pow, mul_pow]
    field_simp
  rw [hcol, hbase, mul_pow]
  have hA := one_le_factorial_mul_exp_div_pow k hk
  have hAf : 1 ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f := one_le_pow₀ hA
  have h2 : 1 ≤ (2 : ℝ) ^ f * L := by
    have h := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 2 ^ f)
    rwa [mul_inv_cancel₀ (by positivity)] at h
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f * ((2 : ℝ) ^ f * L) :=
        mul_le_mul hAf h2 zero_le_one (by linarith)
    _ = _ := by ring

theorem stdH_eq (D : D7) (j : ℕ) : Cnt.stdH D.host.E j = massTelescope_form D.host.E j := rfl

theorem stdLat_eq (D : D7) (j : ℕ) : Cnt.stdLat D.host.E j = massTelescope_lat D.host.E j := by
  unfold Cnt.stdLat massTelescope_lat
  congr 2
  funext i
  simp [Pi.basisFun_apply]

theorem massS_eq (D : D7) (j : ℕ) :
    Cnt.massS D j = mass (massTelescope_form D.host.E j) (massTelescope_lat D.host.E j) := by
  unfold Cnt.massS Cnt.massU
  rw [stdH_eq, stdLat_eq]

theorem mass_pred_le : ∀ D : D7, UnitaryVolumeMass.stMassRatio D → Cnt.massS D (D.R.k - 1) ≤ Cnt.massS D D.R.k * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) * (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) := by
  intro D hM
  have hk : 5 ≤ D.R.k := D.R.k_ge
  have hrd : D.host.rdE = 2 * D.host.v := by
    unfold Formalism.BasicNotions.Host.v
    ring
  have hv : 0 < D.host.v := by
    unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))
    exact div_pos (Real.rpow_pos_of_pos hd _) two_pos
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hL := (GlobalTheory.EtaValueBound.lValEta_bounds D.host.E hK D.R.k (by omega)).1
  rw [Formalism.MainNotions.StandardLattice.fDeg_host] at hL
  have hrat := hM D.R.k (by omega) (Fin D.R.k → D.host.E) (Fin (D.R.k - 1) → D.host.E)
    (massTelescope_form D.host.E D.R.k) (massTelescope_form D.host.E (D.R.k - 1))
    (massTelescope_lat D.host.E D.R.k) (massTelescope_lat D.host.E (D.R.k - 1))
    (massTelescope_symm D.host.E _) (massTelescope_symm D.host.E _)
    (massTelescope_ortho D.host.E _) (massTelescope_ortho D.host.E _)
  unfold massRatioRightSide at hrat
  rw [Formalism.MainNotions.StandardLattice.fDeg_host, Formalism.MainNotions.StandardLattice.vInv_host] at hrat
  have key := one_le_ratio_mul D.R.f D.R.k D.host.v (lValEta D.host.E D.R.k) hv (by omega) hL
  rw [massS_eq, massS_eq, hrd]
  set a := mass (massTelescope_form D.host.E D.R.k) (massTelescope_lat D.host.E D.R.k) with ha
  set b := mass (massTelescope_form D.host.E (D.R.k - 1)) (massTelescope_lat D.host.E (D.R.k - 1))
    with hb
  set R := (((D.R.k - 1).factorial : ℝ) * (D.host.v / Real.pi) ^ D.R.k) ^ D.R.f /
    Real.sqrt ((2 * D.host.v) ^ D.R.f) * lValEta D.host.E D.R.k with hR

  have hb0 : 0 ≤ b := by
    rw [hb]
    unfold mass
    split_ifs
    · exact Finset.sum_nonneg fun _ _ => by positivity
    · exact le_rfl
  have hRpos : 0 < R := by
    have h2 : (0 : ℝ) < (2 ^ D.R.f)⁻¹ := by positivity
    have hLpos : 0 < lValEta D.host.E D.R.k := lt_of_lt_of_le h2 hL
    have hpi := Real.pi_pos
    rw [hR]
    positivity
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrat
    linarith
  have hab : a = R * b := by rw [← hrat, div_mul_cancel₀ a hbne]
  rw [hab]
  calc b = b * 1 := (mul_one b).symm
    _ ≤ b * (R * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (2 * (D.R.k : ℝ) * (2 * D.host.v) ^ ((1 : ℝ) / 2)) ^ D.R.f)) :=
        mul_le_mul_of_nonneg_left key hb0
    _ = _ := by ring

end GlobalTheory.MassRatioInvBound
