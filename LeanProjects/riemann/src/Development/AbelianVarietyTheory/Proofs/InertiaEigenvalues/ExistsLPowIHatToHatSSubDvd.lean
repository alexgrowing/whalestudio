import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section Bounded

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

omit [IsUnitBall O K] in

theorem norm_tail_mul_rad_le {f : K⟦X⟧} {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) (n : ℕ) :
    ‖tail l e f n‖ * rad l (1 / e) ^ n ≤ b := by
  have hρ := pow_pos (rad_pos l (1 / e)) n
  rw [← le_div_iff₀ hρ]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (div_nonneg hb hρ.le) fun j => ?_
  rw [le_div_iff₀ hρ, norm_term_eq]
  exact hf _

theorem coeff_sub_E_mul_quotE_of_lt [CompleteSpace K] {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) {n : ℕ}
    (hn : n < e) : coeff n (f - E K l e * quotE l e f) = tail l e f n := by
  rw [tail_rec l e hf n, map_sub, E, add_mul, map_add, coeff_X_pow_mul', if_neg (by omega),
    ← map_natCast (C : K →+* K⟦X⟧) l, coeff_C_mul, quotE, coeff_mk]
  ring

theorem norm_coeff_mul_rad_le_of_mem_S {f : K⟦X⟧} (hf : f ∈ S O K e) (n : ℕ) :
    ‖coeff n f‖ * rad l (1 / e) ^ n ≤ 1 := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hf.1 n)
  refine le_trans ?_ (norm_pow_le_norm_factorial (K := K) l (n / e))
  rw [← rad_pow (K := K) l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le n e)

theorem exists_bdd_div_E_pow [CompleteSpace K] (m : ℕ) {f : K⟦X⟧} (hf : f ∈ Rpi O K l e)
    {b : ℝ} (hb : 0 ≤ b) (hfb : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) :
    ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ b * ‖(l : K)‖⁻¹ ^ m) ∧
      ∃ h ∈ Rpi O K l e, f = g + E K l e ^ m * h := by
  induction m generalizing f b with
  | zero => exact ⟨0, fun n => by simpa using hb, f, hf, by simp⟩
  | succ m ih =>
    have hl0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
    have hl1 : ‖(l : K)‖ < 1 := norm_l_lt_one l
    have hρe : rad l (1 / e) ^ e = ‖(l : K)‖ := rad_pow l e
    have hρ0 : 0 < rad l (1 / e) := rad_pos l _
    have hρ1 : rad l (1 / e) ≤ 1 := rad_le_one l (by positivity)
    have htail := norm_tail_mul_rad_le l e hb hfb
    have hq : ∀ n, ‖coeff n (quotE l e f)‖ * rad l (1 / e) ^ n ≤ b * ‖(l : K)‖⁻¹ := fun n => by
      have := htail (n + e)
      rw [pow_add, hρe] at this
      rw [quotE, coeff_mk, le_mul_inv_iff₀ hl0]
      simpa [mul_assoc] using this
    obtain ⟨g1, hg1, h1, hh1, hq1⟩ :=
      ih (quotE_mem_Rpi l e hf) (mul_nonneg hb (inv_nonneg.2 hl0.le)) hq
    have hpow : ‖(l : K)‖⁻¹ ≤ ‖(l : K)‖⁻¹ ^ (m + 1) := by
      simpa using pow_le_pow_right₀ (one_le_inv₀ hl0 |>.2 hl1.le) (Nat.succ_le_succ (Nat.zero_le m))
    refine ⟨(f - E K l e * quotE l e f) + E K l e * g1, fun n => ?_, h1, hh1, ?_⟩
    · rw [map_add]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rcases lt_or_ge n e with hn | hn
        · rw [coeff_sub_E_mul_quotE_of_lt l e hf hn]
          have h2 := htail n
          have h3 : ‖(l : K)‖ ≤ rad l (1 / e) ^ n := by
            rw [← hρe]; exact pow_le_pow_of_le_one hρ0.le hρ1 hn.le
          have h4 : ‖tail l e f n‖ ≤ b * ‖(l : K)‖⁻¹ := by
            rw [le_mul_inv_iff₀ hl0]
            exact (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2
          exact h4.trans (mul_le_mul_of_nonneg_left hpow hb)
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
          rw [coeff_sub_E_mul_quotE l e hf, norm_zero]
          positivity
      · have hE : ∀ n, ‖coeff n (E K l e)‖ * (1 : ℝ) ≤ 1 := fun n => by
          simpa using (E_mem l e (A O K)) n
        have := norm_coeff_mul_le (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
          (fun _ _ => by simp) (a := 1) (b := b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) zero_le_one
          (by positivity) hE (g := g1) (fun n => by rw [mul_one]; exact hg1 n) n
        have e' : (1 : ℝ) * (b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) = b * ‖(l : K)‖⁻¹ ^ (m + 1) := by
          ring
        rw [mul_one, e'] at this
        exact this
    · linear_combination E K l e * hq1

end Bounded

end GlobalTheory.BK

namespace GlobalTheory.BKReal

open PowerSeries GlobalTheory.BK

theorem exists_l_pow_iHat_toHatS_sub_dvd (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e)
    [CompleteSpace K] (m : ℕ) (s : S O K e) :
    ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣
      (l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) -
        toOD l O y := by
  obtain ⟨g, hg, h, hh, hs⟩ := exists_bdd_div_E_pow l e m (S_le_R l e s.2) zero_le_one
    (norm_coeff_mul_rad_le_of_mem_S l e s.2)
  have hl0 : ‖(l : K)‖ ≠ 0 := norm_ne_zero_iff.2 (GlobalTheory.BK.l_ne_zero (K := K) l)
  have hG : C ((l : K) ^ m) * g ∈ A O K := fun n => by
    rw [coeff_C_mul, norm_mul, norm_pow]
    calc _ ≤ ‖(l : K)‖ ^ m * (1 * ‖(l : K)‖⁻¹ ^ m) := by gcongr; exact hg n
      _ = 1 := by rw [one_mul, ← mul_pow, mul_inv_cancel₀ hl0, one_pow]
  have hH : C ((l : K) ^ m) * h ∈ Rpi O K l e := mul_mem (HasK.C_mem _) hh
  have key : (l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
      (algebraMap (S O K e) (invL l (S O K e)) s) =
      ⟨_, A_le_Rpi l e hG⟩ + EIn l e (Rpi O K l e) ^ m * ⟨_, hH⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_pow, SubringClass.coe_natCast,
      Subalgebra.coe_inclusion, coe_algebraMap_away, coe_EIn, map_pow, map_natCast]
    rw [hs]
    ring
  have e1 : ϖ.iHat O K (toHat O K l e ⟨_, A_le_Rpi l e hG⟩) = toOD l O (ϖ.iA O K ⟨_, hG⟩) :=
    (congrArg (ϖ.iHat O K)
      (toHat_eq_ofAl l e (g := algebraMap (A O K) (invL l (A O K)) ⟨_, hG⟩) rfl)).trans
      (ϖ.iHat_ofA O K _)
  have e2 : ϖ.iHat O K (Ehat O K l e) = ϖ.iAl O K (EIn l e _) := ϖ.iHat_ofAl O K _
  have h1 : (l : OD l O) ^ m *
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) =
      ϖ.iHat O K (toHat O K l e ((l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
        (algebraMap (S O K e) (invL l (S O K e)) s))) := by
    simp only [map_mul, map_pow, map_natCast]
    rfl
  refine ⟨ϖ.iA O K ⟨_, hG⟩, ϖ.iHat O K (toHat O K l e ⟨_, hH⟩), ?_⟩
  rw [h1, key]
  rw [map_add (toHat O K l e), map_add (ϖ.iHat O K), map_mul (toHat O K l e), map_mul (ϖ.iHat O K),
    map_pow (toHat O K l e), map_pow (ϖ.iHat O K), toHat_E, e1, e2]
  ring

end GlobalTheory.BKReal
