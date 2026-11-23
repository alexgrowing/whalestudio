import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrameAbs
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open PowerSeries DualFramesAlt.FrameAbs

variable {O : Type} [CommRing O] [IsDomain O] {d : ℕ}

theorem framepf_cc_subst (Fs g : PowerSeries O) :
    constantCoeff (subst ((X : PowerSeries O) * Fs) g) = constantCoeff g := by
  have h0 : PowerSeries.constantCoeff ((X : PowerSeries O) * Fs) = 0 := by simp
  have ha : PowerSeries.HasSubst ((X : PowerSeries O) * Fs) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h0
  refine (PowerSeries.constantCoeff_subst (R := O) ha g).trans ?_
  rw [finsum_eq_single _ 0]
  · simp
  · intro n hn
    rw [map_pow]
    change coeff n g • (PowerSeries.constantCoeff ((X : PowerSeries O) * Fs)) ^ n = 0
    rw [h0, zero_pow hn, smul_zero]

theorem framepf_mem_span_X (a : PowerSeries O) :
    a ∈ Ideal.span {(X : PowerSeries O)} ↔ constantCoeff a = 0 := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

theorem framepf_mats (c₀ : O) (hc : ∀ y : ℕ, 1 ≤ y → c₀ ^ y ≠ 1) (Fs : PowerSeries O)
    (hF : constantCoeff Fs = c₀) (R : Matrix (Fin d) (Fin d) (PowerSeries O)) (M : ℕ) (hM : 1 ≤ M)
    (aσ lσ : O) (hl : lσ = aσ * ∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) :
    ∃ H H' : Matrix (Fin d) (Fin d) (PowerSeries O),
      (∃ K, H = C lσ • 1 + (X : PowerSeries O) • K) ∧
      (∃ K, (1 + (X : PowerSeries O) • R) * H.map (subst ((X : PowerSeries O) * Fs)) - H =
        (X : PowerSeries O) ^ M • K) ∧
      (∃ K, H' = C lσ • 1 + (X : PowerSeries O) • K) ∧
      (∃ K, H' * (1 + (X : PowerSeries O) • R) - H'.map (subst ((X : PowerSeries O) * Fs)) =
        (X : PowerSeries O) ^ M • K) ∧
      (∃ K, H' * H = C (lσ ^ 2) • 1 + (X : PowerSeries O) ^ M • K) ∧
      (∃ K, H * H' = C (lσ ^ 2) • 1 + (X : PowerSeries O) ^ M • K) := by
  classical
  have hG : HasSubst ((X : PowerSeries O) * Fs) := HasSubst.of_constantCoeff_zero' (by simp)
  set σr : PowerSeries O →+* PowerSeries O := (substAlgHom hG).toRingHom with hσr
  have hσ : ∀ g, σr g = subst ((X : PowerSeries O) * Fs) g := fun g => by
    simp [σr, coe_substAlgHom]
  set Γ : Matrix (Fin d) (Fin d) (PowerSeries O) := 1 + (X : PowerSeries O) • R with hΓ
  set ev : ℕ → PowerSeries O := fun y => C (c₀ ^ y - 1) with hev
  have hAC : ∀ o : O, algebraMap O (PowerSeries O) o = C o := fun o => by
    rw [PowerSeries.algebraMap_apply]; rfl
  have hyp : Hyp O σr Γ X ev := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      rw [framepf_mem_span_X, map_sub, hσ, framepf_cc_subst, sub_self]
    · rw [hΓ, add_sub_cancel_left]
      exact MatIn.smul_self _ _
    · rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
      have : (constantCoeff : PowerSeries O →+* O).mapMatrix Γ = 1 := by
        ext p q
        simp [hΓ, Matrix.one_apply]
      rw [this, Matrix.det_one]
      exact isUnit_one
    · exact mem_nonZeroDivisors_of_ne_zero X_ne_zero
    · intro y
      rw [hσ, subst_pow hG, subst_X hG, hev]
      rw [Ideal.mem_span_singleton]
      obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow Fs (C c₀) y
      have hX : (X : PowerSeries O) ∣ Fs - C c₀ := by
        rw [X_dvd_iff, map_sub, constantCoeff_C, hF, sub_self]
      obtain ⟨u, hu⟩ := hX
      refine ⟨u * t, ?_⟩
      have e : C (c₀ ^ y - 1) + 1 = (C c₀) ^ y := by simp
      rw [e, mul_pow, mul_comm ((C c₀) ^ y), ← mul_sub, ht, hu, pow_succ]
      ring
    · intro y
      rw [hσ, hev, subst_C]
      rfl
    · intro y a hy h
      rw [framepf_mem_span_X] at h ⊢
      rw [map_mul, constantCoeff_C] at h
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (hc y hy))
    · intro o
      rw [hσ, ← PowerSeries.coe_substAlgHom hG, AlgHom.commutes]
    · intro a
      refine ⟨constantCoeff a, ?_⟩
      rw [framepf_mem_span_X, map_sub, hAC, constantCoeff_C, sub_self]
    · intro o h
      rw [framepf_mem_span_X, hAC, constantCoeff_C] at h
      exact h
    · intro y
      exact ⟨c₀ ^ y - 1, by rw [hAC]⟩
  have hD : ∏ y ∈ Finset.Ico 1 M, ev y = C (∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) := by
    rw [hev, map_prod]
  have hc' : ∀ a : PowerSeries O, (∏ y ∈ Finset.Ico 1 M, ev y) * a ∈ Ideal.span {(X : PowerSeries O) ^ M} →
      a ∈ Ideal.span {(X : PowerSeries O) ^ M} := by
    intro a h
    rw [Ideal.mem_span_singleton, X_pow_dvd_iff] at h ⊢
    intro j hj
    have := h j hj
    rw [hD, coeff_C_mul] at this
    exact (mul_eq_zero.1 this).resolve_left
      (Finset.prod_ne_zero_iff.2 fun y hy => sub_ne_zero.2 (hc y (Finset.mem_Ico.1 hy).1))
  obtain ⟨⟨H, hH⟩, -⟩ := exists_frame hyp M hM
  obtain ⟨F, hF'⟩ := exists_dualFrame hyp M hM
  obtain ⟨hFH, hHF⟩ := frame_products hyp M hM H F hH hF' hc'
  have hmap : ∀ Z : Matrix (Fin d) (Fin d) (PowerSeries O), Z.map σr = Z.map (subst ((X : PowerSeries O) * Fs)) := by
    intro Z; ext p q; simp [hσ]
  obtain ⟨K1, hK1⟩ := hH.1.exists_smul
  obtain ⟨K2, hK2⟩ := hH.2.exists_smul
  obtain ⟨K3, hK3⟩ := hF'.1.exists_smul
  obtain ⟨K4, hK4⟩ := hF'.2.exists_smul
  obtain ⟨K5, hK5⟩ := hFH.exists_smul
  obtain ⟨K6, hK6⟩ := hHF.exists_smul
  have hσa : σr (C aσ) = C aσ := by rw [hσ, subst_C]; rfl
  rw [hD] at hK1 hK3 hK5 hK6
  have e1 := (sub_eq_iff_eq_add.1 hK1).trans (add_comm _ _)
  have e3 := (sub_eq_iff_eq_add.1 hK3).trans (add_comm _ _)
  have e5 := (sub_eq_iff_eq_add.1 hK5).trans (add_comm _ _)
  have e6 := (sub_eq_iff_eq_add.1 hK6).trans (add_comm _ _)
  have hsc : ∀ Z : Matrix (Fin d) (Fin d) (PowerSeries O), (C aσ • Z).map σr = C aσ • Z.map σr := by
    intro Z; ext p q; simp [hσa]
  have hsq : C aσ * C aσ * C (∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) ^ 2 = C (lσ ^ 2) := by
    rw [hl, ← map_mul, ← map_pow, ← map_mul]; ring_nf
  refine ⟨C aσ • H, C aσ • F, ⟨C aσ • K1, ?_⟩, ⟨C aσ • K2, ?_⟩, ⟨C aσ • K3, ?_⟩, ⟨C aσ • K4, ?_⟩,
    ⟨(C aσ * C aσ) • K5, ?_⟩, ⟨(C aσ * C aσ) • K6, ?_⟩⟩
  · rw [e1, smul_add, smul_smul, ← map_mul, ← hl, smul_comm (C aσ) (X : PowerSeries O) K1]
  · rw [← hmap, hsc, Matrix.mul_smul, ← smul_sub, hK2, smul_comm]
  · rw [e3, smul_add, smul_smul, ← map_mul, ← hl, smul_comm (C aσ) (X : PowerSeries O) K3]
  · rw [← hmap, hsc, Matrix.smul_mul, ← smul_sub, hK4, smul_comm]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, e5, smul_add, smul_smul, smul_comm _ _ K5, hsq]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, e6, smul_add, smul_smul, smul_comm _ _ K6, hsq]

end Formalism.MainNotions.N.Ln34

end
