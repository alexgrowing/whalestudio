import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IntegrableIteratedFDerivTranslate

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inG_one {n : ℕ} : InG (1 : M2 n) := by simp [InG]

private theorem exists_split_avoiding_of_goodSig (n p q : ℕ) (h : GoodSig n p q) :
    ∃ j ≤ n, (∀ i < j, i ≠ q) ∧ (∀ i < n - j, i ≠ p) ∧ (∀ i < j, i + p ≠ n) ∧ (∀ i < n - j, i + q ≠ n) := by
  unfold GoodSig at h
  rcases h with h | h | h | h
  · exact ⟨min q n, min_le_right _ _, by omega, by omega, by omega, by omega⟩
  · exact ⟨n - min p n, Nat.sub_le _ _, by omega, by omega, by omega, by omega⟩
  · exact ⟨0, Nat.zero_le _, by omega, by omega, by omega, by omega⟩
  · exact ⟨n, le_refl _, by omega, by omega, by omega, by omega⟩

private theorem integral_minorOn_wM_ne_zero {n : ℕ} (j : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g) :
    ∫ k, minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ * (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k))) ∂μ ≠ 0 := by
  have hKk : ∀ k, InK (ι k) := fun k => (hK _).2 ⟨k, rfl⟩
  have hU : ∀ k, wM (ι k) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    intro k
    have h1 := first_cayley_block_unitary (hKk k)
    have h2 := second_cayley_block_unitary (hKk k)
    have hu1 : u1 (ι k) ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 h1
    have hu2 : u2 (ι k) ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 h2
    have hi : (u2 (ι k))⁻¹ = star (u2 (ι k)) := Matrix.inv_eq_right_inv h2
    unfold wM
    rw [hi]
    exact mul_mem (Unitary.star_mem hu2) hu1
  set g : Kg → ℝ := fun k => Complex.normSq (minorOn (blkA j) (wM (ι k))) * Complex.normSq (minorOn (blkB j) (wM (ι k))) with hg
  have hpt : ∀ k, minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ * (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k))) = ((g k : ℝ) : ℂ) := by
    intro k
    rw [minorOn_inv_of_unitary (hU k), minorOn_inv_of_unitary (hU k)]
    simp only [hg, Complex.ofReal_mul, ← Complex.mul_conj, Complex.star_def]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal]
  have hw1 : wM (1 : M2 n) = 1 := by
    have h1 : (1 : M2 n) = Matrix.fromBlocks 1 0 0 1 := Matrix.fromBlocks_one.symm
    unfold wM u1 u2
    rw [h1, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
    simp
  have hm1 : ∀ s : Finset (Fin n), minorOn s (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    intro s
    unfold minorOn
    rw [Matrix.submatrix_one _ Subtype.val_injective]
    simp
  have hcw : Continuous fun k => wM (ι k) :=
    continuousOn_wM.comp_continuous hι (fun k => det_second_cayley_block_ne_zero (hKk k).1)
  have hgc : Continuous g := by
    rw [hg]
    exact ((Complex.continuous_normSq.comp ((continuous_minorOn _).comp hcw))).mul
      (Complex.continuous_normSq.comp ((continuous_minorOn _).comp hcw))
  have hpos : 0 < ∫ k, g k ∂μ := by
    refine hgc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (HasCompactSupport.of_compactSpace _) (fun k => ?_) ?_
    · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    · simp [hg, map_one, hw1, hm1]
  exact_mod_cast hpos.ne'

theorem lv_of (hC : Cayley) (hU : UAct) (hDj : DjSec) (hDp : DpDual) (hHI : HolInt) (hHZ : HolZero)
    (hSD : SingToDiff) (hTC : TopComp) (hII : InfInv) : LV := by
  intro n p q hsig Kg _ _ _ _ _ _ μ _ ι hι hK
  by_contra hne
  push_neg at hne
  obtain ⟨j, hjn, hj1, hj2, hj3, hj4⟩ := exists_split_avoiding_of_goodSig n p q hsig
  have hC : ((∏ i ∈ Finset.range j, (-((q:ℤ):ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (-((p:ℤ):ℂ) + (i:ℂ))) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · have := rising_product_ne_zero (-(q:ℤ)) j (fun i hi => by have := hj1 i hi; omega)
      push_cast at this ⊢
      exact this
    · have := rising_product_ne_zero (-(p:ℤ)) (n - j) (fun i hi => by have := hj2 i hi; omega)
      push_cast at this ⊢
      exact this
  have hC' : ((∏ i ∈ Finset.range j, (((p:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (((q:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · have := rising_product_ne_zero ((p:ℤ) - n) j (fun i hi => by have := hj3 i hi; omega)
      push_cast at this ⊢
      exact this
    · have := rising_product_ne_zero ((q:ℤ) - n) (n - j) (fun i hi => by have := hj4 i hi; omega)
      push_cast at this ⊢
      exact this
  have hKk : ∀ k, InK (ι k) := fun k => (hK _).2 ⟨k, rfl⟩
  have hGk : ∀ k, InG (ι k) := fun k => (hKk k).1
  have hfv : ∀ k, (f0 (p:ℤ) (q:ℤ) (ι k))⁻¹ = fV (p:ℤ) (q:ℤ) (ι k) := fun k =>
    (eq_inv_of_mul_eq_one_right (scalar_section_mul_conjugate_section (hKk k) _ _)).symm
  set Ω : Set (M2 n) := {x : M2 n | ∀ k, ι k * x ∈ Dom n} with hΩdef
  have hΩ : IsOpen Ω := isOpen_domK Kg ι hι
  have hGΩ : ∀ g : M2 n, InG g → g ∈ Ω := fun g hg k => gset_sub_dom (inG_mul (hGk k) hg)
  have hf0 : ContDiffOn ℂ ∞ (f0 (p:ℤ) (q:ℤ)) (Dom n) :=
    (contDiffOn_scalar_section (n := n) _ _).mono (fun x hx => dom_sub x hx)
  have hcV : Continuous fun k => fV (p:ℤ) (q:ℤ) (ι k) :=
    cont_on_K _ (contDiffOn_fV _ _) Kg ι hι (fun k => gset_sub_dom (hGk k))
  have hk_cd : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ k : Kg,
      ContDiffOn ℂ ∞ (fun y => F (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k)) Ω := by
    intro F hF k
    exact (hF.comp (contDiff_mulLeft (ι k)).contDiffOn (fun y (hy : y ∈ Ω) => hy k)).mul contDiffOn_const
  set Φ : M2 n → ℂ := fun y => ∫ k, f0 (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ with hΦdef
  have hΦ : ContDiffOn ℂ ∞ Φ Ω :=
    (hHI n Kg μ Ω (fun k y => f0 (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k)) hΩ
      (cont_translate' _ _ isOpen_dom hf0 Kg ι hι _ hcV) (hk_cd _ hf0)).1
  have hD1 : ∀ a b : M2 n, InG a → InG b → detD (fun H : Matrix (Fin n) (Fin n) ℂ => Φ (a * nU H * b)) = 0 := by
    intro a b ha hb
    have hS : IsOpen ((fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) ⁻¹' Ω) :=
      hΩ.preimage (contDiff_nU_sandwich a b).continuous
    have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) ⁻¹' Ω := by
      have hn0 : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
        unfold nU
        exact Matrix.fromBlocks_one
      show a * nU 0 * b ∈ Ω
      rw [hn0, mul_one]
      exact hGΩ _ (inG_mul ha hb)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hS 0 h0
    refine hSD n _ r hr (hΦ.comp (contDiff_nU_sandwich a b).contDiffOn (fun H hH => hball hH)) ?_
    intro ψ hψ
    have h := hne ψ a b hψ ha hb
    rw [fubini_step (p:ℤ) (q:ℤ) Kg μ ι hι hK a b ha hb ψ hψ] at h
    simp only [hfv] at h
    exact h
  have hTop := hTC n j Φ Ω hΩ (fun g hg => hGΩ g hg) hΦ (by
      intro x P S _ _ hP hS
      show ∫ k, f0 (p:ℤ) (q:ℤ) (ι k * (x * mX (1 + P) 0 0 (1 + S))) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ
        = ∫ k, f0 (p:ℤ) (q:ℤ) (ι k * x) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ
      congr 1
      funext k
      rw [← mul_assoc, scalar_section_compact_block_invariant hU j _ _ _ P S hP hS]) hD1
  have hLQ : ∀ (M x : M2 n) (T : Matrix (blkA j) (blkA j) ℂ), LQ (blkA j) (M * x) T = M * LQ (blkA j) x T := by
    intro M x T
    rw [LQ_apply, LQ_apply, mul_assoc]
  have hLR : ∀ (M x : M2 n) (S : Matrix (blkB j) (blkB j) ℂ), LR (blkB j) (M * x) S = M * LR (blkB j) x S := by
    intro M x S
    rw [LR_apply, LR_apply, mul_assoc]
  have hm : ∀ (y : M2 n) (T : Matrix (blkA j) (blkA j) ℂ) (S : Matrix (blkB j) (blkB j) ℂ),
      y * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1 = y + LQ (blkA j) y T + LR (blkB j) y S := by
    intro y T S
    rw [mX_eq, WD_split, LQ_apply, LR_apply, mul_add, mul_add, mul_one, add_assoc]
  have key : ∀ y ∈ Dom n, (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      f0 (p:ℤ) (q:ℤ) (y + LQ (blkA j) y T + LR (blkB j) y S)) =
      ((∏ i ∈ Finset.range j, (-((q:ℤ):ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (-((p:ℤ):ℂ) + (i:ℂ))) * hF j p q y := by
    intro y hy
    have h := hDj n j p q y hjn (dom_sub y hy).1 (dom_sub y hy).2
    simp only [hm] at h
    rw [h]
    unfold hF
    ring
  set Ψ : M2 n → ℂ := fun y => ∫ k, hF j (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ with hΨdef
  have hΨ0 : ∀ g ∈ GSet n, Ψ g = 0 := by
    intro g hg
    have h := hTop g hg
    simp only [hm] at h
    rw [show (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
        Φ (g + LQ (blkA j) g T + LR (blkB j) g S)) = _ from
      spherical_detD hHI (f0 (p:ℤ) (q:ℤ)) hf0 μ ι hι _ hcV (LQ (blkA j)) (LR (blkB j)) hLQ hLR g
        (fun k => hGΩ g hg k)] at h
    have hc : (∫ k, (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
        f0 (p:ℤ) (q:ℤ) (ι k * g + LQ (blkA j) (ι k * g) T + LR (blkB j) (ι k * g) S)) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ) =
        ∫ k, ((∏ i ∈ Finset.range j, (-((q:ℤ):ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (-((p:ℤ):ℂ) + (i:ℂ))) *
          (hF j p q (ι k * g) * fV (p:ℤ) (q:ℤ) (ι k)) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only
      rw [key _ (hGΩ g hg k)]
      ring
    rw [hc, integral_const_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hC
  have hΨc : ContDiffOn ℂ ∞ Ψ Ω :=
    (hHI n Kg μ Ω (fun k y => hF j (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k)) hΩ
      (cont_translate' _ _ isOpen_dom (contDiffOn_hF j _ _) Kg ι hι _ hcV) (hk_cd _ (contDiffOn_hF j _ _))).1
  have hΨd : ∀ N : ℕ, iteratedFDeriv ℂ N Ψ 1 = 0 := fun N =>
    hHZ n Ω Ψ hΩ (fun g hg => hGΩ g hg) hΨc hΨ0 N 1 inG_one
  have hLR' : ∀ (M x : M2 n) (T : Matrix (blkA j) (blkA j) ℂ), LR (blkA j) (M * x) T = M * LR (blkA j) x T := by
    intro M x T
    rw [LR_apply, LR_apply, mul_assoc]
  have hLQ' : ∀ (M x : M2 n) (S : Matrix (blkB j) (blkB j) ℂ), LQ (blkB j) (M * x) S = M * LQ (blkB j) x S := by
    intro M x S
    rw [LQ_apply, LQ_apply, mul_assoc]
  have hsph := spherical_detD hHI (hF j (p:ℤ) (q:ℤ)) (contDiffOn_hF j _ _) μ ι hι _ hcV
    (LR (blkA j)) (LQ (blkB j)) hLR' hLQ' 1 (fun k => hGΩ 1 inG_one k)
  have hzero : (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      Ψ (1 + LR (blkA j) 1 T + LQ (blkB j) 1 S)) = 0 := by
    rw [detD_detD_comp Ψ Ω hΩ hΨc 1 (hGΩ 1 inG_one) (LR (blkA j) 1) (LQ (blkB j) 1)]
    simp [hΨd]
  rw [show (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      Ψ (1 + LR (blkA j) 1 T + LQ (blkB j) 1 S)) = _ from hsph] at hzero
  have htr := transpose_detD hII (hF j (p:ℤ) (q:ℤ)) (fV (p:ℤ) (q:ℤ)) (c1 (p:ℤ) (q:ℤ)) (c2 (p:ℤ) (q:ℤ))
    (contDiffOn_hF j _ _) (contDiffOn_fV _ _) (fun P x hP hx => hF_law j _ _ hP hx)
    (fun P x hP hx => fV_law _ _ hP hx) (fun P hP => modulus_characters_product _ _ hP) Kg μ ι hι hK
    (LR (blkA j) 1) (LQ (blkB j) 1) (by
      intro T T' S S'
      simp only [LR_apply, LQ_apply, one_mul]
      rw [add_comm (WD 0 _), add_comm (WD 0 _), ← WD_add, ← WD_add, add_zero, zero_add, add_zero, zero_add]
      exact WD_mul_WD_B_A j T S T' S')
  have e1 : ∀ (k : Kg) (T : Matrix (blkA j) (blkA j) ℂ) (S : Matrix (blkB j) (blkB j) ℂ),
      ι k * 1 + LR (blkA j) (ι k * 1) T + LQ (blkB j) (ι k * 1) S = ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S := by
    intro k T S
    simp only [LR_apply, LQ_apply, mul_one, one_mul]
  simp only [e1] at hzero
  rw [htr] at hzero
  have e2 : ∀ (y : M2 n) (T : Matrix (blkA j) (blkA j) ℂ) (S : Matrix (blkB j) (blkB j) ℂ),
      y + y * LR (blkA j) 1 T + y * LQ (blkB j) 1 S = y * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1 := by
    intro y T S
    rw [mX_eq, WD_split, LR_apply, LQ_apply, one_mul, one_mul, mul_add, mul_add, mul_one, add_assoc, add_comm (y * WD 0 _)]
  simp only [e2] at hzero
  have hc : (∫ k, hF j (p:ℤ) (q:ℤ) (ι k) * (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      fV (p:ℤ) (q:ℤ) (ι k * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1)) ∂μ) =
      ∫ k, ((∏ i ∈ Finset.range j, (((p:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (((q:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) *
        (minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ *
          (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k)))) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [hDp n j p q (ι k) hjn (hGk k)]
    have h1 := scalar_section_mul_conjugate_section (hKk k) (p:ℤ) (q:ℤ)
    unfold hF
    linear_combination ((∏ i ∈ Finset.range j, (((p:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (((q:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) *
        (minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ *
          (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k)))) * h1
  rw [hc, integral_const_mul] at hzero
  exact integral_minorOn_wM_ne_zero j Kg μ ι hι hK
    ((mul_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left (pow_ne_zero _ (by norm_num)))).resolve_left hC')

end PositivityTheory.Rg.Sw.LVs
