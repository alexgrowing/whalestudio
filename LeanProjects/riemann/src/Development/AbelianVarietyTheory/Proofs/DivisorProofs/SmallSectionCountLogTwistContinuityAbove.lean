import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogNcardSeminormBallExpSmallLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBallsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountNearbyPowersSecondBundleLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsMulLeQuotientPowerTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSectionBallOfMulSmallSectionPowTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountTwistExpRadiusLePowSuccStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem log_add_log_le_of_mul_le_mul (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ c * d) (hce : c ≤ e) :
    Real.log a + Real.log b ≤ Real.log e + Real.log d := by
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcd : 1 ≤ c * d := hab.trans h
  have hc : c ≠ 0 := by rintro rfl; simp at hcd
  have hd : d ≠ 0 := by rintro rfl; simp at hcd
  have he : e ≠ 0 := by omega
  have h1 : Real.log ((a : ℝ) * b) ≤ Real.log ((e : ℝ) * d) := by
    apply Real.log_le_log
    · have : (1 : ℝ) ≤ (a : ℝ) * b := by exact_mod_cast hab
      linarith
    · have : a * b ≤ e * d := h.trans (Nat.mul_le_mul_right d hce)
      exact_mod_cast this
  rwa [Real.log_mul (by exact_mod_cast (by omega : a ≠ 0)) (by exact_mod_cast (by omega : b ≠ 0)),
    Real.log_mul (by exact_mod_cast he) (by exact_mod_cast hd)] at h1

theorem lc_add_div_sub_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c →
    Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
    P.lc M ((M / n : ℕ) - c) 1 ≤ P.lc M (-c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hD P b s t hG c hgen hreg ε hε
  have hfin : ∀ (a c : ℤ) (R : ℝ), (P.Bl a c R).Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hD P
  have hball : ∀ a c : ℤ, IsBallFam (P.H a c) (P.Bl a c) := GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P
  have hpos : ∀ (a c : ℤ) (R : ℝ), 0 ≤ R → 1 ≤ (P.Bl a c R).ncard := fun a c R hR =>
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (hfin a c R)).mpr ⟨0, (hball a c).zero_mem R hR⟩).ne'
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.log_count_twist_exp_radius_le_pow_succ k X p D hD P b s t hG c hreg
  obtain ⟨δ, hδ, hrad⟩ := GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le X.functionField (fun N => P.H (N : ℤ) (-c)) (fun N => P.Bl (N : ℤ) (-c))
    (D + 1) (Nat.succ_pos D) (fun N => hball N _) (fun N R => hfin N _ R) C0 hC0 (ε / 2) (by positivity)
  obtain ⟨C, hC, hdiv⟩ := GlobalTheory.T.mem_sectionBall_of_mul_smallSection_pow_twist k X p D hD P c hgen s hG.s_mem.1 hG.s_ne (δ / 3) (by positivity)
  have hdA := GlobalTheory.T.log_count_nearby_powers_second_bundle_le k X p D hD P b c hG.pos hreg (ε / 2) (by positivity)
  have hn : ∀ᶠ n : ℕ in atTop, 3 * C / δ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hdA, hn] with n hdAn hnC
  filter_upwards [hdAn, hrad, hn] with M hdm hradm hMC
  have hnδ : 3 * C ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnC
  have hMδ : 3 * C ≤ (M : ℝ) * δ := (div_le_iff₀ hδ).mp hMC
  have hmn : ((M / n : ℕ) : ℝ) * n ≤ M := by exact_mod_cast Nat.div_mul_le_self M n
  generalize M / n = m at *
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m

  have hrad_le : Real.exp (δ / 3 * (M : ℝ) + C * m + C) ≤ Real.exp (δ * (M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hnδ hm0, mul_le_mul_of_nonneg_right hmn hδ.le]
  have hSsub : {f | f ∈ P.H M (-c) ∧ f * s ^ m ∈ P.Bl M (m - c) 2} ⊆ P.Bl M (-c) (Real.exp (δ * (M : ℝ))) := by
    rintro f ⟨hf1, hf2⟩
    have hf := hdiv M m f hf1 hf2
    exact ⟨hf.1, fun σ y => (hf.2 σ y).trans hrad_le⟩
  have hEfin := hfin M (-c) (Real.exp (δ * (M : ℝ)))
  have hSfin := hEfin.subset hSsub
  have hlev := GlobalTheory.T.encard_small_sections_mul_le_quotient_power_twist k X p D hD P b s t hG c M m
  rw [← (hfin _ _ _).cast_ncard_eq, ← (hfin _ _ _).cast_ncard_eq, ← hSfin.cast_ncard_eq,
    ← (hfin _ _ _).cast_ncard_eq] at hlev
  have hnat : ∀ x y z w : ℕ, (x : ℕ∞) * y ≤ z * w → x * y ≤ z * w := fun x y z w h => by exact_mod_cast h
  have hkey := log_add_log_le_of_mul_le_mul _ _ _ _ _ (hpos _ _ _ zero_le_one) (hpos _ _ _ zero_le_one)
    (hnat _ _ _ _ hlev)
    (Set.ncard_le_ncard hSsub hEfin)
  simp only [Pair.lc] at hdm ⊢
  linarith

end GlobalTheory.HSNef
