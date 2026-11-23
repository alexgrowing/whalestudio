import Formalism.HermitianCurvature.HermitianCurvatureProofs.Lam1
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

theorem qU_pos : 0 < qU := by
  unfold qU
  have hβ : U.betaU ≠ 0 := Formalism.FourierDecayAlt.P.scale_matching.2.1
  have hc : 0 < ‖U.betaU‖ / (2 * Real.pi) := div_pos (norm_pos_iff.2 hβ) (by positivity)
  exact_mod_cast Real.toNNReal_pos.2 hc

theorem qU_coe (N : ℕ) : (((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) ^ N : NNReal) : ℝ) : ℂ) = ((qU ^ N : ℝ) : ℂ) := by
  unfold qU; push_cast; rfl

theorem exists_hMat_n (a : C.LPt) (ha : ∀ b ∈ a, 1 ≤ b.1 ∧ b.2 ≠ 0) (n : ℕ) (hn : D.ptSize a = n) :
    ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), U.hMat σ d = D.ptMatN a n := by
  subst hn
  obtain ⟨σ, d, -, hM⟩ := PBJ.Asm.exists_hMat a ha
  exact ⟨σ, d, hM⟩

section vec

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem vec_om {n : ℕ} (vec : C.LPt → V) (Φ0 : G.Mat n → V) (hΦ0 : PBJ.KCls Φ0)
    (hV : ∀ (a : C.LPt) (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), D.IsLocPt a n → U.hMat σ d = D.ptMatN a n →
      vec a = U.PhiTop (p := n) (s := 0) U.betaU σ d Φ0 fun x => x.elim0)
    (H : C.LPt) (hH : ∀ b ∈ H, 1 ≤ b.1 ∧ b.2 ≠ 0) (m : ℕ) (hn : D.ptSize H + (m + 1 + 1) = n) :
    ∃ (σh : Equiv.Perm (Fin (D.ptSize H))) (dh : Fin (D.ptSize H) → ℂ) (Ψ0 : G.Mat (D.ptSize H + (m + 1 + 1)) → V),
      (∀ i, dh i ≠ 0) ∧ PBJ.KCls Ψ0 ∧
      (∀ t c : ℂ, t ≠ 0 → c ≠ 0 → vec (H ++ [(m + 1, t), (1, c)]) =
        (((qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))))⁻¹ : ℝ) : ℂ) •
          G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) t c) ∧
      (∀ z : ℂ, z ≠ 0 → vec (H ++ [(m + 1 + 1, z)]) =
        (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) z) := by
  subst hn
  have hβ : U.betaU ≠ 0 := Formalism.FourierDecayAlt.P.scale_matching.2.1
  obtain ⟨σh, dh, hdh, hMh⟩ := PBJ.Asm.exists_hMat H hH
  refine ⟨σh, dh, Φ0, hdh, hΦ0, ?_, ?_⟩
  · intro t c ht hc
    set a := H ++ [(m + 1, t), (1, c)] with ha
    have hloc : D.IsLocPt a (D.ptSize H + (m + 1 + 1)) := by
      refine ⟨fun b hb => ?_, ?_⟩
      · rcases List.mem_append.1 hb with hb | hb
        · exact hH b hb
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact ⟨by omega, ht⟩
          · exact ⟨le_rfl, hc⟩
      · rw [ha, PBJ.Asm.ptSize_append]; simp [D.ptSize]
    obtain ⟨σ, d, hM⟩ := exists_hMat_n a hloc.1 _ hloc.2
    have hdb : ∀ i, PBJ.Om.dB (m + 1) t c i ≠ 0 := by
      intro i
      induction i using Fin.addCases with
      | left j => simp only [PBJ.Om.dB, PBJ.Fub.dQ, Fin.addCases_left]; exact ht
      | right j => simp only [PBJ.Om.dB, PBJ.Fub.dQ, Fin.addCases_right]; exact hc
    have e1 := PBJ.Asm.ptMatN_append H [(m + 1, t), (1, c)]
    have hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat (PBJ.Om.σB (m + 1)) (PBJ.Om.dB (m + 1) t c)) := by
      rw [hM, hMh, PBJ.Om.hMat_block, ← PBJ.Asm.ptMatN_block]; exact e1
    rw [hV a σ d hloc hM, PBJ.fubini_head_last_part U.betaU (D.ptSize H) (m + 1 + 1) σ d σh dh (PBJ.Om.σB (m + 1))
      (PBJ.Om.dB (m + 1) t c) V Φ0 hdh hdb hM' hΦ0]
    rw [PBJ.Om.omBlock_eq U.betaU (m + 1) t c, qU_coe, smul_smul, Fintype.card_fin]
    have hq : (qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))) : ℝ) ≠ 0 := pow_ne_zero _ qU_pos.ne'
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hq, Complex.ofReal_one, one_smul]
    rfl
  · intro z hz
    set a := H ++ [(m + 1 + 1, z)] with ha
    have hloc : D.IsLocPt a (D.ptSize H + (m + 1 + 1)) := by
      refine ⟨fun b hb => ?_, ?_⟩
      · rcases List.mem_append.1 hb with hb | hb
        · exact hH b hb
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl
          exact ⟨by omega, hz⟩
      · rw [ha, PBJ.Asm.ptSize_append]; simp [D.ptSize]
    obtain ⟨σ, d, hM⟩ := exists_hMat_n a hloc.1 _ hloc.2
    have hMb : U.hMat (Fin.revPerm : Equiv.Perm (Fin (m + 1 + 1))) (fun _ => z) =
        D.ptMatN [(m + 1 + 1, z)] (D.ptSize [(m + 1 + 1, z)]) := by
      rw [PBJ.Asm.hMat_rev]; exact (PBJ.Asm.ptMatN_long (m + 1 + 1) z).symm
    have hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat Fin.revPerm (fun _ => z)) := by
      rw [hM, hMh, hMb]; exact PBJ.Asm.ptMatN_append H [(m + 1 + 1, z)]
    rw [hV a σ d hloc hM, PBJ.fubini_head_last_part U.betaU (D.ptSize H) (m + 1 + 1) σ d σh dh Fin.revPerm (fun _ => z) V Φ0
      hdh (fun _ => hz) hM' hΦ0]
    rw [PBJ.Om.omLong_eq U.betaU (m + 1) z, qU_coe, smul_smul]
    have hq : (qU ^ Fintype.card (G.UT (m + 1 + 1)) : ℝ) ≠ 0 := pow_ne_zero _ qU_pos.ne'
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hq, Complex.ofReal_one, one_smul]

end vec

section rho

theorem one_sub_pow_le (u : ℝ) (hu0 : 0 ≤ u) (n : ℕ) : 1 - u ^ n ≤ n * (1 - u) := by
  have := one_add_mul_le_pow (a := u - 1) (by linarith) n
  simp only [add_sub_cancel] at this
  linarith

theorem rho_fac (δ : ℝ) (hδ : 0 < δ) (k N : ℕ) (u : ℝ) (hu1 : δ ≤ u) (hu2 : u ≤ 1) :
    |√(u ^ k) * √((u⁻¹) ^ N)| ≤ √((δ⁻¹) ^ N) ∧
      |√(u ^ k) * √((u⁻¹) ^ N) - 1| ≤ (k + N * (δ⁻¹) ^ N) * (1 - u) := by
  have hu0 : 0 < u := lt_of_lt_of_le hδ hu1
  have hk0 : 0 ≤ u ^ k := pow_nonneg hu0.le k
  have hk1 : u ^ k ≤ 1 := pow_le_one₀ hu0.le hu2
  have hi1 : 1 ≤ u⁻¹ := one_le_inv₀ hu0 |>.2 hu2
  have hiδ : u⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hu1
  have hN1 : 1 ≤ (u⁻¹) ^ N := one_le_pow₀ hi1
  have hNδ : (u⁻¹) ^ N ≤ (δ⁻¹) ^ N := pow_le_pow_left₀ (by positivity) hiδ N
  set f := √(u ^ k) * √((u⁻¹) ^ N) with hf
  have hf0 : 0 ≤ f := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hf2 : f ^ 2 = u ^ k * (u⁻¹) ^ N := by
    rw [hf, mul_pow, Real.sq_sqrt hk0, Real.sq_sqrt (by positivity)]
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg hf0, hf]
    calc √(u ^ k) * √((u⁻¹) ^ N) ≤ 1 * √((δ⁻¹) ^ N) := by
          refine mul_le_mul ?_ (Real.sqrt_le_sqrt hNδ) (Real.sqrt_nonneg _) zero_le_one
          rw [Real.sqrt_le_one]; exact hk1
      _ = √((δ⁻¹) ^ N) := one_mul _
  ·
    have h1 : |f - 1| ≤ |f ^ 2 - 1| := by
      have : f ^ 2 - 1 = (f - 1) * (f + 1) := by ring
      rw [this, abs_mul]
      have : 1 ≤ |f + 1| := by rw [abs_of_nonneg (by linarith)]; linarith
      nlinarith [abs_nonneg (f - 1)]
    have hA : 1 - u ^ k ≤ k * (1 - u) := one_sub_pow_le u hu0.le k
    have hB : (u⁻¹) ^ N - 1 ≤ N * (δ⁻¹) ^ N * (1 - u) := by
      have e : (u⁻¹) ^ N - 1 = (u⁻¹) ^ N * (1 - u ^ N) := by
        rw [mul_sub, mul_one, ← mul_pow, inv_mul_cancel₀ hu0.ne', one_pow]
      rw [e]
      have hC := one_sub_pow_le u hu0.le N
      have h0 : 0 ≤ 1 - u ^ N := by linarith [pow_le_one₀ (n := N) hu0.le hu2]
      calc (u⁻¹) ^ N * (1 - u ^ N) ≤ (δ⁻¹) ^ N * (N * (1 - u)) :=
            mul_le_mul hNδ hC h0 (by positivity)
        _ = N * (δ⁻¹) ^ N * (1 - u) := by ring
    have h2 : |f ^ 2 - 1| ≤ (k + N * (δ⁻¹) ^ N) * (1 - u) := by
      rw [hf2]
      have e : u ^ k * (u⁻¹) ^ N - 1 = u ^ k * ((u⁻¹) ^ N - 1) - (1 - u ^ k) := by ring
      rw [e]
      have ha : 0 ≤ u ^ k * ((u⁻¹) ^ N - 1) := mul_nonneg hk0 (by linarith)
      have hb : u ^ k * ((u⁻¹) ^ N - 1) ≤ N * (δ⁻¹) ^ N * (1 - u) :=
        le_trans (mul_le_of_le_one_left (by linarith) hk1) hB
      rw [abs_le]; constructor <;> nlinarith
    linarith

theorem rho_bound (TT ε0 dH0 MK mK : ℝ) (hTT : 0 < TT) (hε0 : 0 < ε0) (hdH0 : 0 ≤ dH0) (hmK : 0 < mK)
    (k N m : ℕ) (l1 x y c : ℂ) (hl1 : l1 ≠ 0) (hx : x ≠ 0) (hy0 : y ≠ 0) (hc0 : c ≠ 0) (hyM : ‖y‖ ≤ MK)
    (hym : mK ≤ ‖y‖) (hnc : Complex.normSq c = ‖x‖ ^ (2 * (m + 1)) * ‖y‖ ^ 2)
    (hA : ε0 ≤ dH0 * ‖l1 * x⁻¹‖ ^ (2 * (m + 1)) * (Complex.normSq c - TT)) :
    |√((Complex.normSq c - TT) ^ k) / ‖c‖ ^ k * √((Complex.normSq c / (Complex.normSq c - TT)) ^ N)| ≤
        √(((ε0 / (max dH0 1 * ‖l1‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N) ∧
      |√((Complex.normSq c - TT) ^ k) / ‖c‖ ^ k * √((Complex.normSq c / (Complex.normSq c - TT)) ^ N) - 1| ≤
        ((k : ℝ) + N * ((ε0 / (max dH0 1 * ‖l1‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N) *
          (TT / mK ^ 2) * ‖x‖⁻¹ ^ (2 * (m + 1)) := by
  set n := 2 * (m + 1) with hn
  set δ := ε0 / (max dH0 1 * ‖l1‖ ^ n * (max MK 1) ^ 2) with hδ
  set GG := Complex.normSq c - TT with hGG
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hl1pos : 0 < ‖l1‖ := norm_pos_iff.2 hl1
  have hncpos : 0 < Complex.normSq c := by rw [hnc]; positivity
  have hnt : ‖l1 * x⁻¹‖ ^ n = ‖l1‖ ^ n * (‖x‖ ^ n)⁻¹ := by
    rw [norm_mul, norm_inv, mul_pow, inv_pow]
  rw [hnt] at hA
  have hGGpos : 0 < GG := by
    by_contra hle
    have : dH0 * (‖l1‖ ^ n * (‖x‖ ^ n)⁻¹) * GG ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hle)
    linarith
  set u := GG / Complex.normSq c with hu
  have hu0 : 0 ≤ u := div_nonneg hGGpos.le hncpos.le
  have huy : u * ‖y‖ ^ 2 = GG * (‖x‖ ^ n)⁻¹ := by
    rw [hu, hnc]; field_simp
  have hu1 : δ ≤ u := by
    have hden : 0 < max dH0 1 * ‖l1‖ ^ n * (max MK 1) ^ 2 := by positivity
    rw [hδ, div_le_iff₀ hden]
    have hyM' : ‖y‖ ^ 2 ≤ (max MK 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hyM.trans (le_max_left _ _)) 2
    calc ε0 ≤ dH0 * (‖l1‖ ^ n * (‖x‖ ^ n)⁻¹) * GG := hA
      _ = dH0 * ‖l1‖ ^ n * (u * ‖y‖ ^ 2) := by rw [huy]; ring
      _ ≤ max dH0 1 * ‖l1‖ ^ n * (u * (max MK 1) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
            (mul_le_mul_of_nonneg_left hyM' hu0) (by positivity) (by positivity)
      _ = u * (max dH0 1 * ‖l1‖ ^ n * (max MK 1) ^ 2) := by ring
  have hu2 : u ≤ 1 := by
    rw [hu, div_le_one hncpos, hGG]; linarith
  have h1u : 1 - u ≤ TT / mK ^ 2 * (‖x‖ ^ n)⁻¹ := by
    have e : 1 - u = TT / Complex.normSq c := by
      rw [hu, hGG]; field_simp; ring
    rw [e, hnc]
    have hmy : mK ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hmK.le hym 2
    calc TT / (‖x‖ ^ n * ‖y‖ ^ 2) ≤ TT / (‖x‖ ^ n * mK ^ 2) :=
          div_le_div_of_nonneg_left hTT.le (by positivity) (mul_le_mul_of_nonneg_left hmy (by positivity))
      _ = TT / mK ^ 2 * (‖x‖ ^ n)⁻¹ := by field_simp
  have hρu : √(GG ^ k) / ‖c‖ ^ k * √((Complex.normSq c / GG) ^ N) = √(u ^ k) * √((u⁻¹) ^ N) := by
    have hinv : Complex.normSq c / GG = u⁻¹ := by rw [hu, inv_div]
    rw [hinv]
    congr 1
    have hcn : ‖c‖ ^ 2 = Complex.normSq c := (Complex.normSq_eq_norm_sq c).symm
    have hGu : GG = u * ‖c‖ ^ 2 := by rw [hcn, hu, div_mul_cancel₀ _ hncpos.ne']
    rw [hGu, mul_pow, Real.sqrt_mul (pow_nonneg hu0 _), ← pow_mul, mul_comm 2, pow_mul,
      Real.sqrt_sq (pow_nonneg (norm_nonneg _) _)]
    have : ‖c‖ ^ k ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hc0)
    field_simp
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨hb1, hb2⟩ := rho_fac δ hδpos k N u hu1 hu2
  rw [hρu]
  refine ⟨hb1, hb2.trans ?_⟩
  rw [mul_assoc, inv_pow ‖x‖ n]
  exact mul_le_mul_of_nonneg_left h1u (by positivity)

end rho

end

end Formalism.FourierDecayAlt.P.GermRateSplit
