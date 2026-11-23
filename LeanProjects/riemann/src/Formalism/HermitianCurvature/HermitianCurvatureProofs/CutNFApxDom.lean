import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def DominatedL2TruncationBound : Prop :=
  ∀ Cb C₁ : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ Th : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th →
      ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ n : ℕ, ∀ᵐ c : Fin (P.r + 1) → ℂ,
        ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
          TBB.Ew p (fun _ => 1) (B.opApply Th (fun g => cutN P.k P.r n g • f g)) (P.r + 1) [] (TBB.bigPt P.r c) ≤ h c

section cutn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem apx_cutF_fpm {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) (ε : ℝ) (n : ℕ) :
    apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n =
      D.cutF p.T.base χ (TBBx4.fpm p (fun g => cutN P.k P.r n g • f g) (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε := by
  funext g
  simp only [apx, D.cutF, TBBx4.fpm, ContinuousLinearMap.smul_comp, smul_smul]
  congr 1
  ring

theorem cutN_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn (⊤ : ℕ∞) (B.GV k r) f) (n : ℕ) :
    B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => cutN k r n g • f g) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
    simp_rw [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutN k r n) := by
    unfold cutN
    refine Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ?_)
    refine ContDiff.div_const (contDiff_const.sub ?_) _
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    exact hN.comp ((contDiff_apply_apply ℝ ℂ i j).comp (contDiff_const_smul _))
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
  refine ⟨U, fun g => cutN k r n g • f' g, hU, hgU, hc.contDiffOn.smul hf', fun g hg hgv => ?_⟩
  show cutN k r n g • f g = cutN k r n g • f' g
  rw [hff g hg hgv]

theorem cutN_ccle_unif {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E) (A : ℝ)
    (m : ℕ) (bf : ℝ) (hbf : B.CCle A m f bf) :
    ∃ b : ℝ, ∀ n : ℕ, B.CCle (A - 1) m (fun g => cutN k r n g • f g) b := by
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := k) (r := r) (E := E) m
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) m f bf := BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  refine ⟨bf + Kp * bf, fun n => ?_⟩
  have hψ : B.CCle (A - 1) m (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) (Kp * bf / ((n : ℝ) + 1)) :=
    hKp _ (by positivity) A f bf hbf
  have e : (fun g => cutN k r n g • f g) = fun g => f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    funext g
    rw [PBE.cut_eq (fun n g => cutN k r n g) (fun n g => rfl) n g]
    rw [sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
  rw [e]
  refine JCx2.pd_ccle_mono_c (BetaSesquilinearity.CCle_add hbf' (BetaSesquilinearity.CCle_smul (-1) hψ)) ?_
  have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  simp only [norm_neg, norm_one, one_mul]
  linarith

end cutn

theorem nfApxDomAll_of_cut (hZ : NFDomZero) (hP : NFDomPtw) (hU : DominatedL2TruncationBound) : NFApxDomAll := by
  intro Cb
  obtain ⟨C1, C₁, H1⟩ := hP Cb
  obtain ⟨C2, H2⟩ := hU Cb C₁
  refine ⟨max C1 C2 + 1, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  obtain ⟨hχ, hCb, hf, hfA, hth, hN2⟩ := hH
  set X : ℝ := ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)
    with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have h3 : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have h2 : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    have h4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
    have h5 : 1 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by linarith
    rw [hX]
    nlinarith
  have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) = x * X := fun x => by rw [hX]; ring
  rw [e] at hth
  have hunif : ∀ m : ℕ, ∃ b : ℝ, ∀ n, B.CCle (A₀ - 1) m (fun g => cutN P.k P.r n g • f g) b := fun m => by
    obtain ⟨bf, hbf⟩ := hfA m
    exact cutN_ccle_unif f A₀ m bf hbf
  have h2 : (max C1 C2 + 1) * X = max C1 C2 * X + X := by ring
  have hyp : ∀ c, c ≤ max C1 C2 → ∀ n : ℕ,
      NFHyp Cb c p (fun g => cutN P.k P.r n g • f g) (A₀ - 1) p₀ χ N := fun c hc n => by
    refine ⟨hχ, hCb, cutN_ckOn hf n, fun m => ?_, ?_, hN2⟩
    · obtain ⟨b, hb⟩ := hunif m
      exact ⟨b, hb n⟩
    · rw [e]
      have h1 : c * X ≤ max C1 C2 * X := mul_le_mul_of_nonneg_right hc (by linarith)
      linarith
  have hyp0 : NFHyp Cb C2 p f A₀ p₀ χ N := by
    refine ⟨hχ, hCb, hf, hfA, ?_, hN2⟩
    rw [e]
    have h1 : C2 * X ≤ max C1 C2 * X := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    linarith
  obtain ⟨m, Th, Mb, hMb, hok, hb⟩ := H1 Wp Wq P p p₀ χ Y N w hw hN
  choose hh hhi hhb using fun t => H2 Wp Wq P p f A₀ p₀ χ N hyp0 (Th t) (hok t)
  refine ⟨fun c => Mb * ∑ t, |hh t c|, (integrable_finsetSum Finset.univ fun t _ => (hhi t).abs).const_mul Mb,
    fun n => ?_⟩
  filter_upwards [ae_all_iff.2 fun t => hhb t n] with c hc
  rw [apx_cutF_fpm]
  by_cases hc' : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  · exact le_trans (hb (fun g => cutN P.k P.r n g • f g) (A₀ - 1) (hyp C1 (le_max_left _ _) n) ε hε c hc'.1 hc'.2)
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => (hc t).trans (le_abs_self _)) hMb)
  · rw [hZ Wp Wq P p _ w c hc', norm_zero]
    exact mul_nonneg hMb (Finset.sum_nonneg fun t _ => abs_nonneg _)

end

end Formalism.FourierDecayAlt.P.CutBP
