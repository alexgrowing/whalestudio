import Mathlib
import Formalism.PeriodIntegrals.IdxCalc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IndexCalculation.SmulMemSpanSmul

noncomputable section

namespace PI.Dv.IdxW

open NumberField IsDedekindDomain Module

theorem dvIdxCalc_main : PI.Dv.IdxCalc := by
  intro K _ _ V _ _ _ _ w M N hM hN hMN
  obtain ⟨c, hc0, hcMN⟩ := den_of_span (K := K) M N hM hMN
  obtain ⟨e, he0, heNM⟩ := den_of_span (K := K) N M hN hMN.symm
  have h1 : lenAt w M N ≠ ⊤ := lenS_ne_top w M N hM hc0 hcMN
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro P hP hPN
    obtain ⟨c2, hc2, hc2MP⟩ := den_of_span (K := K) M P hM (hMN.trans hPN.symm)
    obtain ⟨e2, he2, he2PM⟩ := den_of_span (K := K) P M hP (hPN.trans hMN.symm)
    set D := Ideal.span {c * c2} • M with hD
    have hDM : D ≤ M := Submodule.smul_le_right
    have hDN : D ≤ N := span_smul_le _ M N (fun x hx => by
      rw [mul_comm, mul_smul]
      exact N.smul_mem c2 (hcMN x hx))
    have hDP : D ≤ P := span_smul_le _ M P (fun x hx => by
      rw [mul_smul]
      exact P.smul_mem c (hc2MP x hx))
    have fM : lenS w.asIdeal.primeCompl M D ≠ ⊤ :=
      lenS_ne_top w M D hM (mul_ne_zero hc0 hc2) (fun x hx => smul_mem_span_smul _ M hx)
    have fN : lenS w.asIdeal.primeCompl N D ≠ ⊤ :=
      lenS_ne_top w N D hN (mul_ne_zero (mul_ne_zero hc0 hc2) he0) (fun x hx => by
        rw [mul_smul]
        exact smul_mem_span_smul _ M (heNM x hx))
    have fP : lenS w.asIdeal.primeCompl P D ≠ ⊤ :=
      lenS_ne_top w P D hP (mul_ne_zero (mul_ne_zero hc0 hc2) he2) (fun x hx => by
        rw [mul_smul]
        exact smul_mem_span_smul _ M (he2PM x hx))
    rw [idx_via w M P D hDM hDP fM fP, idx_via w M N D hDM hDN fM fN,
      idx_via w N P D hDN hDP fN fP]
    ring
  ·
    intro V' _ _ _ _ φ
    set φ' := φ.restrictScalars (𝓞 K) with hφ'
    set k := (LinearMap.ker φ).restrictScalars (𝓞 K) with hkdef
    have hk : ∀ x, x ∈ k ↔ φ' x = 0 := fun x => by
      rw [hkdef, Submodule.restrictScalars_mem, LinearMap.mem_ker]
      rfl
    set D := Ideal.span {c} • M with hD
    have hDM : D ≤ M := Submodule.smul_le_right
    have hDN : D ≤ N := span_smul_le c M N hcMN
    have hce : c * e ≠ 0 := mul_ne_zero hc0 he0
    have hNin : ∀ x ∈ N, (c * e) • x ∈ D := fun x hx => by
      rw [mul_smul]
      exact smul_mem_span_smul c M (heNM x hx)
    have fMD : lenS w.asIdeal.primeCompl M D ≠ ⊤ :=
      lenS_ne_top w M D hM hc0 (fun x hx => smul_mem_span_smul c M hx)
    have fND : lenS w.asIdeal.primeCompl N D ≠ ⊤ := lenS_ne_top w N D hN hce hNin
    have hMk : (M ⊓ k).FG := Submodule.FG.of_le hM inf_le_left
    have hNk : (N ⊓ k).FG := Submodule.FG.of_le hN inf_le_left
    have fMk : lenS w.asIdeal.primeCompl (M ⊓ k) (D ⊓ k) ≠ ⊤ :=
      lenS_ne_top w _ _ hMk hc0 (fun x hx => ⟨smul_mem_span_smul c M hx.1, k.smul_mem c hx.2⟩)
    have fNk : lenS w.asIdeal.primeCompl (N ⊓ k) (D ⊓ k) ≠ ⊤ :=
      lenS_ne_top w _ _ hNk hce (fun x hx => ⟨hNin x hx.1, k.smul_mem _ hx.2⟩)
    have fMi : lenS w.asIdeal.primeCompl (M.map φ') (D.map φ') ≠ ⊤ :=
      lenS_ne_top w _ _ (hM.map φ') hc0 (by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨c • x, smul_mem_span_smul c M hx, by rw [map_smul]⟩)
    have fNi : lenS w.asIdeal.primeCompl (N.map φ') (D.map φ') ≠ ⊤ :=
      lenS_ne_top w _ _ (hN.map φ') hce (by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨(c * e) • x, hNin x hx, by rw [map_smul]⟩)
    have eM := lenS_ker_img w.asIdeal.primeCompl φ' k hk D M hDM
    have eN := lenS_ker_img w.asIdeal.primeCompl φ' k hk D N hDN
    rw [idx_via w M N D hDM hDN fMD fND,
      idx_via w (M ⊓ k) (N ⊓ k) (D ⊓ k) (inf_le_inf_right k hDM) (inf_le_inf_right k hDN) fMk fNk,
      idx_via w (M.map φ') (N.map φ') (D.map φ') (Submodule.map_mono hDM) (Submodule.map_mono hDN)
        fMi fNi, eM, eN, ENat.toNat_add fMk fMi, ENat.toNat_add fNk fNi]
    push_cast
    ring
  ·
    intro F hF
    set N' := N ⊓ (w.asIdeal ^ F) • M with hN'
    have hloc : ∀ x ∈ N, ∃ s ∈ w.asIdeal.primeCompl, s • x ∈ N' := fun x hx => by
      obtain ⟨s, hs, hsx⟩ := hF x hx
      exact ⟨s, Ideal.mem_primeCompl_iff.mpr hs, N.smul_mem s hx, hsx⟩
    have hwM : (w.asIdeal ^ F) • M ≤ M := Submodule.smul_le_right
    have hN'MN : N' ≤ M ⊓ N := le_inf (inf_le_right.trans hwM) inf_le_left
    have h0 : lenAt w N M = 0 := by
      rw [lenAt_eq, lenS_inf]
      refine nonpos_iff_eq_zero.mp ?_
      calc lenS w.asIdeal.primeCompl N (N ⊓ M) ≤ lenS w.asIdeal.primeCompl N N' :=
            lenS_le _ N' (N ⊓ M) N (le_inf inf_le_left (hN'MN.trans inf_le_left)) inf_le_left
        _ = 0 := lenS_eq_zero _ N N' hloc
    have hge : ((F * Formalism.HN.rkK M : ℕ) : ℕ∞) ≤ lenAt w M N := by
      rw [lenAt_eq, lenS_inf]
      have a1 := lenS_add w.asIdeal.primeCompl N' (M ⊓ N) M hN'MN inf_le_left
      have a2 := lenS_add w.asIdeal.primeCompl N' ((w.asIdeal ^ F) • M) M inf_le_right hwM
      have a3 : lenS w.asIdeal.primeCompl (M ⊓ N) N' = 0 :=
        lenS_eq_zero _ _ _ (fun x hx => hloc x hx.2)
      rw [a3, add_zero] at a1
      rw [← a1, a2, len_pow w M hM F]
      exact le_self_add
    unfold idxAt
    rw [h0]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h1
    rw [← hn] at hge ⊢
    have hle : F * Formalism.HN.rkK M ≤ n := by exact_mod_cast hge
    simp only [ENat.toNat_coe, ENat.toNat_zero, Nat.cast_zero, sub_zero]
    exact_mod_cast hle
  ·
    intro F
    have hwM : (w.asIdeal ^ F) • M ≤ M := Submodule.smul_le_right
    unfold idxAt
    rw [lenAt_eq, lenAt_eq, len_pow w M hM F, lenS_of_le _ _ _ hwM]
    simp only [ENat.toNat_coe, ENat.toNat_zero, Nat.cast_zero, sub_zero]
    push_cast
    ring
  ·
    intro n hn hNM hnMN
    have hc : ((n : ℕ) : 𝓞 K) ≠ 0 := by
      intro h
      have h' : ((n : ℕ) : K) = 0 := by
        rw [← map_natCast (algebraMap (𝓞 K) K) n, h, map_zero]
      exact hn.ne' (by exact_mod_cast h')
    obtain ⟨k, hk, hlen⟩ := len_c w M hM hc
    have hle1 : Ideal.span {((n : ℕ) : 𝓞 K)} • M ≤ N := span_smul_le _ M N hnMN
    have hle2 := lenS_le w.asIdeal.primeCompl _ N M hle1 hNM
    rw [hlen] at hle2
    have hv : Formalism.BasicNotions.vAdd w ((n : ℕ) : K) = k := by
      rw [← map_natCast (algebraMap (𝓞 K) K) n]
      exact hk
    unfold idxAt
    rw [lenAt_eq, lenAt_eq, lenS_of_le _ N M hNM, hv]
    have hfin : lenS w.asIdeal.primeCompl M N ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle2
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hm] at hle2 ⊢
    have hle : m ≤ k * Formalism.HN.rkK M := by exact_mod_cast hle2
    simp only [ENat.toNat_coe, ENat.toNat_zero, Nat.cast_zero, sub_zero]
    calc (m : ℤ) ≤ ((k * Formalism.HN.rkK M : ℕ) : ℤ) := by exact_mod_cast hle
      _ = (Formalism.HN.rkK M : ℤ) * (k : ℤ) := by push_cast; ring

end PI.Dv.IdxW
