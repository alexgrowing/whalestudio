import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CanonicalPsiNeZeroOfPathBasis
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DerivProdRangeSubMulProdNeZero
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContinuousMatrixLowerRightBlock
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.StepD

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem vacuum_nonvanishing_of_facts (hFd : FdProps) (hDj : DjFd) (hKS : KSplit) (hSph : SphU) (hFz : FzHol) : Crux0 := by
  intro n m hmn Kg _ _ _ _ _ _ μ _ ι hι hK
  by_contra hneg
  push Not at hneg
  set j : ℕ := n - m with hjdef
  have hjn : j ≤ n := Nat.sub_le n m
  have hj1 : 1 ≤ j := by omega
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hιK : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩

  set ΩZ : Set (M2 n) := {x | ∀ k, ι k * x ∈ DomZ n} with hΩZdef
  have hΩZo : IsOpen ΩZ := isOpen_setK (hFz n m 0).1 Kg ι hι
  have hGΩZ : GSet n ⊆ ΩZ := fun g hg k => (hFz n m 0).2.1 (inG_mul (hιG k) hg)
  have hDZ : ∀ y ∈ DomZ n, y ∈ Dom n := fun y hy => hy.1
  have hFdCD : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := ((hFd n m).1).of_le le_top

  set ρ : Matrix (Fin n) (Fin n) ℂ → Kg → ℂ := fun Y => rhoP ι m 0 Y with hρdef
  have hρc : ∀ Y, Continuous (ρ Y) := fun Y => CrxMa.continuous_rhoP hFz m ι hι hιG Y
  set Φ : Matrix (Fin n) (Fin n) ℂ → M2 n → ℂ := fun Y x => ∫ k, Fd m (ι k * x) * ρ Y k ∂μ with hΦdef
  have hΦ : ∀ Y, ContDiffOn ℂ ∞ (Φ Y) ΩZ := fun Y =>
    (holInt n Kg μ ΩZ (fun k x => Fd m (ι k * x) * ρ Y k) hΩZo
      (fun N => (continuousOn_iteratedFDeriv_translate (Fd m) (DomZ n) (hFz n m 0).1 hFdCD Kg ι hι _ (hρc Y) N).mono
        (Set.prod_mono subset_rfl (fun x hx => hx)))
      (fun k => (hFdCD.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ ΩZ) => hx k)).mul contDiffOn_const)).1

  have stepA : ∀ Y a b, InG a → InG b → detD (fun H => Φ Y (a * nU H * b)) = 0 :=
    fun Y a b ha hb => CrxMa.stepA_Z hFd hFz m Kg μ ι hι hK hneg Y a b ha hb

  have stepB : ∀ Y g, InG g → detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      Φ Y (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) = 0 := by
    intro Y
    refine topComp n j (Φ Y) ΩZ hΩZo hGΩZ (hΦ Y) ?_ (stepA Y)
    intro x P' S' hxM hx hP hS
    simp only [hΦdef]
    congr 1; funext k
    rw [← mul_assoc, Fd_kpart m j (ι k * x) (hDZ _ (hx k)) P' S' hP hS]

  set a1 : ℂ := deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0
  have ha1 : a1 ≠ 0 := deriv_prod_range_sub_mul_prod_ne_zero n m hmn
  set Ψ : Matrix (Fin n) (Fin n) ℂ → M2 n → ℂ := fun Y x => ∫ k, hF j m 0 (ι k * x) * ρ Y k ∂μ with hΨdef
  have stepC : ∀ Y g, InG g → Ψ Y g = 0 := fun Y g hg =>
    Cx3.stepC hFd hDj hSph hFz m j hj1 hjn ha1 μ ι hι hιG (ρ Y) (hρc Y) (fun g hg => stepB Y g hg) g hg

  have stepD : ∀ Y (N : ℕ) (W : Fin N → M2 n) (g : M2 n), InG g →
      ∫ k, iteratedFDeriv ℂ N (hF j m 0) (ι k * g) (fun i => ι k * g * W i) * ρ Y k ∂μ = 0 := fun Y N W g hg =>
    Cx3.stepD j (m : ℤ) 0 μ ι hι hιG (ρ Y) (hρc Y) (fun g hg => stepC Y g hg) N W g hg

  have stepE : ∀ (N : ℕ) (v : Fin (N + 1) → M2 n) (a0 b0 : Fin n), v 0 = WD 0 (Matrix.single a0 b0 1) →
      (∀ a b, v a * v b = 0) →
      ∫ k, iteratedFDeriv ℂ (N + 1) (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i) * fV (m : ℤ) 0 (ι k) ∂μ = 0 := by
    intro N v a0 b0 hv0 hv
    have hdom : ∀ k, ι k ∈ Dom n := fun k => gset_sub_dom (hιG k)
    set F1 : M2 n → ℂ := rit (hF j (m : ℤ) 0) N (fun i => v i.succ) with hF1def
    have hF1 : ContDiffOn ℂ ∞ F1 (Dom n) := rit_contDiffOn _ _ isOpen_dom (contDiffOn_hF j (m : ℤ) 0) N _
    have hF1law : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = c1 (m : ℤ) 0 P * F1 x :=
      rit_law _ (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) (c1 (m : ℤ) 0) (fun P x hP hx => mul_mem_dom hP hx)
        (fun P x hP hx => hF_law j (m : ℤ) 0 hP hx) N _
    have e1 : ∀ k, iteratedFDeriv ℂ (N + 1) (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i) =
        rit F1 1 (fun _ => v 0) (ι k) := by
      intro k
      rw [← rit_eq (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) (N + 1) v hv (ι k) (hdom k)]
      rfl
    have hT := rit_transpose infInv F1 (c1 (m : ℤ) 0) (c2 (m : ℤ) 0) hF1 hF1law (fun P hP => modulus_characters_product (m : ℤ) 0 hP)
      Kg μ ι hι hK 1 (fV (m : ℤ) 0) (contDiffOn_fV (m : ℤ) 0) (fun P x hP hx => fV_law (m : ℤ) 0 hP hx)
      (fun _ => v 0) (fun a b => hv 0 0)
    simp_rw [e1]
    rw [hT]
    have e2 : ∀ k, rit (fV (m : ℤ) 0) 1 (fun i => (fun _ : Fin 1 => v 0) (Fin.rev i)) (ι k) =
        ((m : ℂ) - n) * (fV (m : ℤ) 0 (ι k) * ((u1 (ι k))⁻¹ * u2 (ι k)) b0 a0) := by
      intro k
      show fderiv ℂ (fV (m : ℤ) 0) (ι k) (ι k * v 0) = _
      rw [hv0, fderiv_fV_R m (ι k) (hdom k) a0 b0]; ring
    obtain ⟨L, c, kl, hKl⟩ := hKS n m a0 b0 Kg ι hK
    have := GlobalTheory.isMulRightInvariant_of_compactSpace μ
    have hF1c : Continuous fun k => F1 (ι k) := cont_on_K F1 hF1 Kg ι hι hdom
    have e3 : ∀ l, ∫ k, F1 (ι k) * rhoP ι m 0 1 (k * kl l) ∂μ = 0 := by
      intro l
      have h := integral_mul_right_eq_self (μ := μ) (fun k => F1 (ι (k * (kl l)⁻¹)) * rhoP ι m 0 1 k) (kl l)
      simp only [mul_inv_cancel_right] at h
      rw [h]
      have hg : InG (ι (kl l)⁻¹) := hιG _
      have := stepD 1 N (fun i => v i.succ) (ι (kl l)⁻¹) hg
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [map_mul]
      rw [hF1def, rit_eq (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) N _ (fun a b => hv _ _)
        _ (gset_sub_dom (inG_mul (hιG k) hg))]
    have e4 : ∀ k, F1 (ι k) * rit (fV (m : ℤ) 0) 1 (fun i => (fun _ : Fin 1 => v 0) (Fin.rev i)) (ι k) =
        ((m : ℂ) - n) * ∑ l, c l * (F1 (ι k) * rhoP ι m 0 1 (k * kl l)) := by
      intro k; rw [e2, hKl k, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e4]
    rw [integral_const_mul, integral_finsetSum]
    · simp_rw [integral_const_mul, e3, mul_zero, Finset.sum_const_zero]; simp
    · intro l _
      exact Integrable.const_mul (integrable_of_continuous_K μ (hF1c.mul ((hρc 1).comp (continuous_id.mul continuous_const)))) _

  have stepE' : ∀ (K : ℕ) (v : Fin K → M2 n) (i0 : Fin K) (a0 b0 : Fin n), v i0 = WD 0 (Matrix.single a0 b0 1) →
      (∀ a b, v a * v b = 0) →
      ∫ k, iteratedFDeriv ℂ K (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i) * fV (m : ℤ) 0 (ι k) ∂μ = 0 := by
    intro K v i0 a0 b0 hvi hv
    obtain ⟨N, rfl⟩ : ∃ N, K = N + 1 := ⟨K - 1, by have := i0.2; omega⟩
    set σ : Equiv.Perm (Fin (N + 1)) := Equiv.swap 0 i0 with hσ
    have hsym : ∀ k, iteratedFDeriv ℂ (N + 1) (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i) =
        iteratedFDeriv ℂ (N + 1) (hF j (m : ℤ) 0) (ι k) (fun i => ι k * (v ∘ σ) i) := by
      intro k
      have := TC.iterSymm (M2 n) (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) (ι k)
        (gset_sub_dom (hιG k)) (N + 1) (fun i => ι k * v i) σ
      rw [← this]; rfl
    simp_rw [hsym]
    refine stepE N (v ∘ σ) a0 b0 ?_ (fun a b => hv _ _)
    simp [hσ, hvi]
  have hLRLQ : ∀ (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
      (T' : Matrix (blkA (n := n) j) (blkA j) ℂ) (S' : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (LR (blkA j) 1 T + LQ (blkB j) 1 S) * (LR (blkA j) 1 T' + LQ (blkB j) 1 S') = 0 := by
    intro T S T' S'
    rw [LR_apply, LQ_apply, LR_apply, LQ_apply, one_mul, one_mul, one_mul, one_mul, add_comm (WD 0 _), ← WD_add,
      add_zero, zero_add, add_comm (WD 0 _), ← WD_add, add_zero, zero_add]
    exact WD_mul_WD_B_A j T S T' S'
  have hDc : ∀ (K : ℕ) (v : Fin K → M2 n), (∀ a b, v a * v b = 0) →
      Continuous (fun k => iteratedFDeriv ℂ K (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i)) := by
    intro K v hv
    have e : (fun k => iteratedFDeriv ℂ K (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i)) =
        fun k => rit (hF j (m : ℤ) 0) K v (ι k) := by
      funext k
      rw [rit_eq (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) K v hv (ι k) (gset_sub_dom (hιG k))]
    rw [e]
    exact cont_on_K _ (rit_contDiffOn _ _ isOpen_dom (contDiffOn_hF j (m : ℤ) 0) K v) Kg ι hι
      (fun k => gset_sub_dom (hιG k))
  have hfVc : Continuous (fun k => fV (m : ℤ) 0 (ι k)) :=
    cont_on_K _ (contDiffOn_fV (m : ℤ) 0) Kg ι hι (fun k => gset_sub_dom (hιG k))
  have stepF : ∫ k, detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      hF j (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) * fV (m : ℤ) 0 (ι k) ∂μ = 0 := by
    have hcA : Fintype.card (blkA (n := n) j) = j := card_blkA hjn
    have e : ∀ k, detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        hF j (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) =
        ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
          (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
          iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (hF j (m : ℤ) 0) (ι k)
            (fun i => ι k * Fin.append
              (fun i => LR (blkA j) 1 (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
                (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
              (fun i => LQ (blkB j) 1 (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
                (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)) i) := by
      intro k
      have := detD_detD_comp (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) (ι k)
        (gset_sub_dom (hιG k)) ((mulL (ι k)).comp (LR (blkA j) 1)) ((mulL (ι k)).comp (LQ (blkB j) 1))
      simp only [ContinuousLinearMap.comp_apply, mulL_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
      rw [fin_append_mul]
    simp_rw [e, Finset.sum_mul]
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero fun σ _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_eq_zero fun τ _ => ?_
        simp_rw [mul_assoc]
        rw [integral_const_mul, integral_const_mul]
        refine mul_eq_zero_of_right _ (mul_eq_zero_of_right _ ?_)
        have h0 : 0 < Fintype.card (blkA (n := n) j) := by omega
        refine stepE' _ _ (Fin.castAdd _ ⟨0, h0⟩) ((Fintype.equivFin (blkA (n := n) j)).symm ⟨0, h0⟩ : Fin n)
          (σ ((Fintype.equivFin (blkA (n := n) j)).symm ⟨0, h0⟩) : Fin n) ?_ ?_
        · rw [Fin.append_left, LR_apply, one_mul, embOn_single_pf]
        · intro a b
          refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
            simp only [Fin.append_left, Fin.append_right]
          · simpa using hLRLQ _ 0 _ 0
          · simpa using hLRLQ _ 0 0 _
          · simpa using hLRLQ 0 _ _ 0
          · simpa using hLRLQ 0 _ 0 _
      · intro τ _
        refine integrable_of_continuous_K μ (((continuous_const.mul (hDc _ _ ?_)).mul hfVc))
        intro a b
        refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
          simp only [Fin.append_left, Fin.append_right]
        · simpa using hLRLQ _ 0 _ 0
        · simpa using hLRLQ _ 0 0 _
        · simpa using hLRLQ 0 _ _ 0
        · simpa using hLRLQ 0 _ 0 _
    · intro σ _
      refine integrable_finsetSum _ fun τ _ => ?_
      refine integrable_of_continuous_K μ (((continuous_const.mul (hDc _ _ ?_)).mul hfVc))
      intro a b
      refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
        simp only [Fin.append_left, Fin.append_right]
      · simpa using hLRLQ _ 0 _ 0
      · simpa using hLRLQ _ 0 0 _
      · simpa using hLRLQ 0 _ _ 0
      · simpa using hLRLQ 0 _ 0 _

  have hWz : ∀ (T T' : Matrix (blkA (n := n) j) (blkA j) ℂ) (S S' : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (LR (blkA j) 1 T + LQ (blkB j) 1 S) * (LR (blkA j) 1 T' + LQ (blkB j) 1 S') = 0 := by
    intro T T' S S'
    have e : ∀ (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ),
        LR (blkA j) 1 T + LQ (blkB j) 1 S = WD (embOn (blkB j) S) (embOn (blkA j) T) := by
      intro T S
      rw [LR_apply, LQ_apply, one_mul, one_mul, add_comm, ← WD_add, add_zero, zero_add]
    rw [e, e]; exact WD_mul_WD_B_A j T S T' S'
  have weight_sum_eq := transpose_detD infInv (hF j (m : ℤ) 0) (fV (m : ℤ) 0) (c1 (m : ℤ) 0) (c2 (m : ℤ) 0)
    (contDiffOn_hF j (m : ℤ) 0) (contDiffOn_fV (m : ℤ) 0)
    (fun P' x hP hx => hF_law j (m : ℤ) 0 hP hx) (fun P' x hP hx => fV_law (m : ℤ) 0 hP hx)
    (fun P' hP => modulus_characters_product (m : ℤ) 0 hP) Kg μ ι hι hK (LR (blkA j) 1) (LQ (blkB j) 1) hWz
  rw [stepF] at weight_sum_eq
  have stepE3 : ∫ k, hF j (m : ℤ) 0 (ι k) * detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ =>
      detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        fV (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) ∂μ = 0 := by
    have hs : ((-1 : ℂ) ^ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j))) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.1 weight_sum_eq.symm).resolve_left hs
  have hcst' : (∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · rw [Finset.prod_ne_zero_iff]
      intro i hi
      rw [Finset.mem_range] at hi
      have : ((m : ℤ) : ℂ) - n + i = (((m : ℤ) - n + i : ℤ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (by omega : (m : ℤ) - n + i ≠ 0)
    · rw [Finset.prod_ne_zero_iff]
      intro i hi
      rw [Finset.mem_range] at hi
      have : ((0 : ℤ) : ℂ) - n + i = (((0 : ℤ) - n + i : ℤ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (by omega : (0 : ℤ) - n + i ≠ 0)
  have stepG : ∫ k, (((‖minorOn (blkA j) (wM (ι k))‖ ^ 2 * ‖minorOn (blkB j) (wM (ι k))‖ ^ 2 : ℝ)) : ℂ) ∂μ = 0 := by
    have e : ∀ k, hF j (m : ℤ) 0 (ι k) * detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ =>
        detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fV (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) =
        ((∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i))) *
          (((‖minorOn (blkA j) (wM (ι k))‖ ^ 2 * ‖minorOn (blkB j) (wM (ι k))‖ ^ 2 : ℝ)) : ℂ) := by
      intro k
      have r : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fV (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) =
          (fun T => detD (fun S => fV (m : ℤ) 0 (ι k * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1))) := by
        funext T; congr 1; funext S
        rw [mul_mX, LR_apply, LQ_apply, one_mul, one_mul, add_assoc, add_assoc, add_comm (ι k * WD 0 _)]
      rw [r, dpDual cayley uAct n j (m : ℤ) 0 (ι k) hjn (hιG k)]
      have hu := wM_mem_unitary (hιK k)
      rw [minorOn_inv_of_unitary hu, hF, minorOn_inv_of_unitary hu]
      have h1 := scalar_section_mul_conjugate_section (hιK k) (m : ℤ) 0
      have ha : minorOn (blkA j) (wM (ι k)) * star (minorOn (blkA j) (wM (ι k))) =
          ((‖minorOn (blkA j) (wM (ι k))‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hb : minorOn (blkB j) (wM (ι k)) * star (minorOn (blkB j) (wM (ι k))) =
          ((‖minorOn (blkB j) (wM (ι k))‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast at ha hb
      rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
      linear_combination (((∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i))) *
        minorOn (blkA j) (wM (ι k)) * star (minorOn (blkA j) (wM (ι k))) * minorOn (blkB j) (wM (ι k)) *
        star (minorOn (blkB j) (wM (ι k)))) * h1 + 0 * ha + 0 * hb +
        (((∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i))) *
          (minorOn (blkB j) (wM (ι k)) * star (minorOn (blkB j) (wM (ι k))))) * ha +
        (((∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i))) *
          (‖minorOn (blkA j) (wM (ι k))‖ ^ 2 : ℂ)) * hb
    simp_rw [e, integral_const_mul] at stepE3
    exact (mul_eq_zero.1 stepE3).resolve_left hcst'
  have hpos := pos_int j Kg μ ι hι hK
  rw [integral_complex_ofReal] at stepG
  exact hpos.ne' (by exact_mod_cast stepG)

end PositivityTheory.Rg.Sw.HSt
