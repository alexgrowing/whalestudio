import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PgFrameAtRecord
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CriticalLevelLePowAllPlacesStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem levelPrime_size : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → C0 * Real.exp 8 ≤ D.R.k → LocalBesselAndTopKernel.FamilyMidVolume D → ∀ u, large₂.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m : ℝ)) := by
  intro hS hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl hCu hC0 hR u
  obtain ⟨hF, hA, -, hk⟩ := pgFrame_at_record hS hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl hCu hC0 hR
  have hcrit := GlobalTheory.T.criticalLevel_le_pow_allPlaces hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl
  obtain ⟨hS0, hData, hC01⟩ := hH
  dsimp only [StandingHypotheses] at hS0
  obtain ⟨-, -, hm4, hfk, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, hv, -, -, -, -, hClm, -⟩ := hS0
  have hwin := (hData.2.2.2.2.2.2.2.2.2.1 u).2

  have hLpos : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hb : 1 < large₂.sc.b := by
    have := Real.add_one_le_exp large₂.sc.L
    show 1 < Real.exp large₂.sc.L
    linarith
  have hbpos : 0 < large₂.sc.b := by linarith
  have hm40 : (40:ℝ) ≤ D.R.m := le_trans hCl hClm
  have hmk : ((D.R.m + 3 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  push_cast at hmk
  have hk40 : (40:ℝ) ≤ D.R.k := by linarith
  have hkpos : (0:ℝ) < D.R.k := by linarith
  have hfpos : (0:ℝ) < D.R.f := by
    have h1 : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_trans h1 hm4)
  have hfk' : (D.R.f:ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hrS : 2 * D.R.rS + 2 = D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    omega

  have hkb : 0 < (D.R.k:ℝ) * large₂.sc.b := mul_pos hkpos hbpos
  have hgg : ((D.R.k:ℝ) * large₂.sc.b) ^ 16 ≤ gg D := by
    show _ ≤ (D.host.g 0 : ℝ) * D.host.g 1
    have h0 : 0 ≤ ((D.R.k:ℝ) * large₂.sc.b) ^ 8 := (pow_pos hkb 8).le
    calc ((D.R.k:ℝ) * large₂.sc.b) ^ 16 = ((D.R.k:ℝ) * large₂.sc.b) ^ 8 * ((D.R.k:ℝ) * large₂.sc.b) ^ 8 := by ring
      _ ≤ _ := mul_le_mul hg1 hg2 h0 (le_trans h0 hg1)
  have hggpos : 0 < gg D := lt_of_lt_of_le (pow_pos hkb 16) hgg

  have hka_pos : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
  have hka_le : D.host.ka ≤ 4 := by
    show Real.pi / D.host.v ≤ 4
    rw [div_le_iff₀ (by linarith)]
    linarith [Real.pi_le_four]
  have hK_pos : 0 < Bridge.kaS D := div_pos hka_pos hggpos
  have hK : Bridge.kaS D * large₂.sc.b ^ 16 ≤ 1 := by
    show D.host.ka / gg D * large₂.sc.b ^ 16 ≤ 1
    rw [div_mul_eq_mul_div, div_le_one hggpos]
    have hk16 : (D.R.k:ℝ) ≤ (D.R.k:ℝ) ^ 16 := le_self_pow₀ (by linarith) (by norm_num)
    have hb16 : 0 ≤ large₂.sc.b ^ 16 := (pow_pos hbpos 16).le
    calc D.host.ka * large₂.sc.b ^ 16 ≤ 4 * large₂.sc.b ^ 16 := mul_le_mul_of_nonneg_right hka_le hb16
      _ ≤ (D.R.k:ℝ) ^ 16 * large₂.sc.b ^ 16 := mul_le_mul_of_nonneg_right (by linarith) hb16
      _ = ((D.R.k:ℝ) * large₂.sc.b) ^ 16 := by ring
      _ ≤ gg D := hgg
  unfold Formalism.L2.SG.RowsConc.TFrameAt at hF
  have hT0 : 0 ≤ Tr D u := Nat.cast_nonneg _
  have hlow : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ Tr D u := by
    have h1 := hF u
    have h2 : (Bridge.kaS D * large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ 1 :=
      pow_le_one₀ (mul_pos hK_pos (pow_pos hbpos 16)).le hK
    rw [mul_pow] at h2
    have hP : 0 ≤ (large₂.sc.b ^ 16) ^ (2 * D.R.rS) := (pow_pos (pow_pos hbpos 16) _).le
    have e : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) * (Tr D u * Bridge.kaS D ^ (2 * D.R.rS)) =
        Tr D u * (Bridge.kaS D ^ (2 * D.R.rS) * (large₂.sc.b ^ 16) ^ (2 * D.R.rS)) := by ring
    linarith [mul_le_mul_of_nonneg_left h1 hP, mul_le_mul_of_nonneg_left h2 hT0]
  refine ⟨le_trans ?_ hlow, ?_⟩
  · rw [← pow_mul, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb.le
    have : ((2 * D.R.rS + 2 : ℕ) : ℝ) = D.R.m := by exact_mod_cast hrS
    push_cast at this ⊢
    linarith
  ·
    by_contra hup
    push Not at hup
    have hbm : 0 < large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := Real.rpow_pos_of_pos hbpos _
    have hTpos : 0 < Tr D u := lt_trans hbm hup
    obtain ⟨q, hq⟩ : ∃ q, q = large₂.sc.b ^ (-(D.R.m:ℝ)) := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := by rw [hq]; exact (Real.rpow_pos_of_pos hbpos _).le
    have hq1 : q ≤ 1 := by
      rw [hq]; exact (Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)).le
    have hq_eq : large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m:ℝ)) = q * large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := by
      rw [hq, ← Real.rpow_add hbpos]; congr 1; ring
    have hgg0 : 0 ≤ gg D := hggpos.le
    have hTc_pos : ∀ τ, 0 < Tcrit D u τ := by
      intro τ
      have h := hk u τ
      have h1 : (0:ℝ) < (D.R.k:ℝ) ^ (3 * D.R.rS) := pow_pos hkpos _
      by_contra hc
      push Not at hc
      have : gg D ^ (-(D.R.m:ℝ)) * Tcrit D u τ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hgg0 _) hc
      linarith
    have hxpos : ∀ τ, 0 < Tcrit D u τ / Tr D u := fun τ => div_pos (hTc_pos τ) hTpos
    have hx : ∀ τ, Tcrit D u τ / Tr D u ≤ q := by
      intro τ
      rw [div_le_iff₀ hTpos]
      calc Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m:ℝ)) := hcrit u τ
        _ = q * large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := hq_eq
        _ ≤ q * Tr D u := mul_le_mul_of_nonneg_left hup.le hq0
    have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
    obtain ⟨τ0⟩ := hTau
    classical
    have hprod : ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k ≤ q ^ D.R.k := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ0)]
      have hrest : ∏ τ ∈ Finset.univ.erase τ0, (Tcrit D u τ / Tr D u) ^ D.R.k ≤ 1 :=
        Finset.prod_le_one (fun τ _ => pow_nonneg (hxpos τ).le _)
          (fun τ _ => pow_le_one₀ (hxpos τ).le (le_trans (hx τ) hq1))
      calc (Tcrit D u τ0 / Tr D u) ^ D.R.k * ∏ τ ∈ Finset.univ.erase τ0, (Tcrit D u τ / Tr D u) ^ D.R.k
          ≤ (Tcrit D u τ0 / Tr D u) ^ D.R.k * 1 :=
            mul_le_mul_of_nonneg_left hrest (pow_nonneg (hxpos τ0).le _)
        _ ≤ q ^ D.R.k := by rw [mul_one]; exact pow_le_pow_left₀ (hxpos τ0).le (hx τ0) _
    have hP0 : 0 < ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k :=
      Finset.prod_pos (fun τ _ => pow_pos (hxpos τ) _)
    unfold UnitaryVolumeMass.cTvA at hA
    obtain ⟨hlo, hhi⟩ := hA u
    have hQ : 0 < D.what₂.Dstar / (D.duS u : ℝ) := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hP0) hlo
    have hd : 0 < (D.duS u : ℝ) := by
      rcases (Nat.cast_nonneg (D.duS u) : (0:ℝ) ≤ _).eq_or_lt with h | h
      · rw [← h, div_zero] at hQ
        exact absurd hQ (lt_irrefl 0)
      · exact h
    have hDs : 0 < D.what₂.Dstar := by
      have := mul_pos hQ hd
      rwa [div_mul_cancel₀ _ hd.ne'] at this
    have hC0pos : 0 < C0 := by linarith

    have hlogG : 0 < Real.log (D.mem u).A.GamP := by
      rw [large₂.Gam_eq u]
      have hL0 : 0 < large₂.sc.L := by linarith
      have hm0 : (0:ℝ) < D.R.m := by linarith
      exact mul_pos (mul_pos (mul_pos large₂.CGam_pos (pow_pos hm0 5)) hfpos) hL0
    have hG0 : (D.mem u).A.GamP ≠ 0 := by
      intro h
      rw [h, Real.log_zero] at hlogG
      exact lt_irrefl 0 hlogG
    have hGabs : 1 < |(D.mem u).A.GamP| := by
      rw [← Real.exp_log_eq_abs hG0]
      have := Real.add_one_le_exp (Real.log (D.mem u).A.GamP)
      linarith
    have hGz : (D.mem u).A.GamP ^ (-2:ℤ) ≤ 1 := by
      rw [zpow_neg, zpow_two]
      apply inv_le_one_of_one_le₀
      rw [← abs_mul_abs_self (D.mem u).A.GamP]
      exact (one_lt_mul_of_lt_of_le hGabs hGabs.le).le
    have hwin' : (D.duS u : ℝ) ≤ 1 * D.what₂.Dstar * C0 :=
      le_trans hwin (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGz hDs.le) hC0pos.le)
    have hinv : 1 / C0 ≤ D.what₂.Dstar / (D.duS u : ℝ) :=
      (div_le_div_iff₀ hC0pos hd).mpr (by linarith)

    have h2pow : (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ 8 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith : (3:ℝ) - D.R.k ≤ 3)
      have h8 : (2:ℝ) ^ (3:ℝ) = 8 := by
        rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      linarith
    have hexp1 : (D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ 8 * D.R.k := by
      calc (D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ (D.R.f:ℝ) * 8 := mul_le_mul_of_nonneg_left h2pow hfpos.le
        _ ≤ 8 * D.R.k := by linarith
    have hqk : q ^ D.R.k = Real.exp (-((D.R.k:ℝ) * large₂.sc.L * D.R.m)) := by
      rw [hq, show large₂.sc.b = Real.exp large₂.sc.L from rfl, ← Real.exp_mul, ← Real.exp_nat_mul]
      congr 1
      ring
    have hLm : (40:ℝ) * D.R.k ≤ (D.R.k:ℝ) * large₂.sc.L * D.R.m := by
      have h40 : (1:ℝ) * 40 ≤ large₂.sc.L * D.R.m := mul_le_mul hLpos.le hm40 (by norm_num) (by linarith)
      rw [mul_assoc]
      linarith [mul_le_mul_of_nonneg_left h40 hkpos.le]
    have hmain : 1 / C0 ≤ Real.exp (-(32 * (D.R.k:ℝ))) := by
      calc 1 / C0 ≤ D.what₂.Dstar / (D.duS u : ℝ) := hinv
        _ ≤ Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k)) * ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k := hhi
        _ ≤ Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k)) * q ^ D.R.k :=
            mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
        _ = Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) - (D.R.k:ℝ) * large₂.sc.L * D.R.m) := by
            rw [hqk, ← Real.exp_add]
            ring_nf
        _ ≤ Real.exp (-(32 * (D.R.k:ℝ))) := Real.exp_le_exp.mpr (by linarith)
    have hC0k : C0 ≤ D.R.k := by
      have h8 := Real.add_one_le_exp 8
      calc C0 = C0 * 1 := (mul_one C0).symm
        _ ≤ C0 * Real.exp 8 := mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
        _ ≤ D.R.k := hC0
    have hkexp : (D.R.k:ℝ) + 1 ≤ Real.exp D.R.k := Real.add_one_le_exp _
    have h31 : Real.exp (-(31 * (D.R.k:ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hsplit : Real.exp (D.R.k:ℝ) * Real.exp (-(32 * (D.R.k:ℝ))) = Real.exp (-(31 * (D.R.k:ℝ))) := by
      rw [← Real.exp_add]
      ring_nf
    have he32 : 0 < Real.exp (-(32 * (D.R.k:ℝ))) := Real.exp_pos _
    have h1C : 1 ≤ C0 * Real.exp (-(32 * (D.R.k:ℝ))) := by
      rw [div_le_iff₀ hC0pos] at hmain
      linarith
    have e : ((D.R.k:ℝ) + 1) * Real.exp (-(32 * (D.R.k:ℝ))) =
        (D.R.k:ℝ) * Real.exp (-(32 * (D.R.k:ℝ))) + Real.exp (-(32 * (D.R.k:ℝ))) := by ring
    linarith [mul_le_mul_of_nonneg_right hC0k he32.le, mul_le_mul_of_nonneg_right hkexp he32.le]

end GlobalTheory
