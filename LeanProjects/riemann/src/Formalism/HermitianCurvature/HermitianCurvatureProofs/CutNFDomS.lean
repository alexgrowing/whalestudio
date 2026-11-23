import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHypS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtwAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DominatedL2TruncationBoundHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomEmpty
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomVMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCutSup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DominatedL2OperatorBoundHolds

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem nfDomPtwS_of_cut (hU : NFUnfoldTop) (hV : NFVMul) (hC : NFCutSup) (hL : NFLeibV) (hN : NFCoreNS)
    (hE : NFEmptyOps) : NFDomPtwS := by
  intro Cb
  obtain ⟨CcL, HL⟩ := hL Cb
  obtain ⟨CcN, C1N, HN⟩ := hN Cb
  obtain ⟨C1E, HE⟩ := hE
  refine ⟨max (max CcL CcN) 0, max C1N C1E, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p p₀ χ Y N w hw hwN
  by_cases hpre : C6.IsCut0 χ ∧ KB.InDDplus2 P p.l0 p.T.base Cb p.Θ ∧ N ≤ 2 * p₀
  swap
  · refine ⟨0, Fin.elim0, 0, le_rfl, fun t => t.elim0, ?_⟩
    intro f A₀ hH
    exact absurd ⟨hH.1, hH.2.1, hH.2.2.2.2.2⟩ hpre
  obtain ⟨hχ, hΘ, hNp⟩ := hpre
  set Mx := max (max CcL CcN) 0 with hMx
  have thr : ∀ C : ℝ, C ≤ Mx → ∀ n : ℕ, n ≤ N → ∀ A : ℝ,
      Mx * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      C * ((P.r : ℝ) + 1) ^ 4 * ((n : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro C hC n hn A hA
    have hM0 : 0 ≤ Mx := le_max_right _ _
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
    have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((n : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
      positivity
    have hXN : ((P.r : ℝ) + 1) ^ 4 * ((n : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
      gcongr
    have e : ∀ (x : ℝ) (m : ℕ), x * ((P.r : ℝ) + 1) ^ 4 * ((m : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
        x * (((P.r : ℝ) + 1) ^ 4 * ((m : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
      fun x m => by ring
    rw [e] at hA ⊢
    exact le_trans (mul_le_mul_of_nonneg_right hC hX) (le_trans (mul_le_mul_of_nonneg_left hXN hM0) hA)
  by_cases hw0 : w = []
  · subst hw0
    obtain ⟨Th₀, Th₁, h0, h1, hap⟩ := HE Wp Wq P p N
    obtain ⟨K, hK⟩ := hC χ hχ 0
    refine ⟨2, ![Th₀, Th₁], K ^ 2, sq_nonneg _, Fin.forall_fin_two.mpr
      ⟨nfOpOK_mono h0 (le_max_right _ _), nfOpOK_mono h1 (le_max_right _ _)⟩, ?_⟩
    intro f A₀ hH hJ ε hε c hl hG
    have hK' : |χ (TBB.Gp p (TBB.bigPt P.r c) / ε)| ≤ K := by simpa using hK ε hε _ hG
    exact nf_empty_bound hV p f p₀ N hNp χ K Th₀ Th₁ hap ε c hl hG hK'
  have hcut : KB.CutWord P p.l0 w := hw.1
  choose Q Lq hLs hLS hLe using fun e : Wd.Ix (Fin w.length) => HL Wp Wq P p hΘ w hcut e
  choose m Th Mb hMb hok hb using
    fun e : Wd.Ix (Fin w.length) => HN Wp Wq P p hΘ Y w hw e (Q e) (Lq e) (hLS e) p₀ N hwN hNp
  choose K hK using fun q : ℕ => hC χ hχ q
  set Ke : Wd.Ix (Fin w.length) → ℝ := fun e => ∑ q : Fin (Q e + 1), |K q| with hKe
  set nT : ℝ := ((Finset.univ : Finset (M.Ty P)).card : ℝ) with hnT
  set Cst : Wd.Ix (Fin w.length) → ℝ := fun e => nT * ((((Q e + 1 : ℕ) : ℝ)) ^ 2 * Ke e ^ 2 * Mb e) with hCst
  have hCst0 : ∀ e, 0 ≤ Cst e := fun e => by
    simp only [hCst]; have := hMb e; positivity
  let ι := Σ e : Wd.Ix (Fin w.length), Fin (m e)
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun i => Th (σ i).1 (σ i).2, ∑ e, Cst e, Finset.sum_nonneg fun e _ => hCst0 e,
    fun i => nfOpOK_mono (hok _ _) (le_max_left _ _), ?_⟩
  intro f A₀ hH hJ ε hε c hl hG
  set γ := TBB.bigPt P.r c with hγ
  set G := TBB.Gp p γ with hGdef
  set F := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hFdef
  have hF : B.CkOn ⊤ (B.GV P.k P.r) F := by
    rw [hFdef, fpm_id]; exact ckOn_Gpow_smul p.T.base.z p.T.base.z' p₀ hH.2.2.1
  have hFcc := inCC_fpm_id p p₀ hH.2.2.2.1
  have hthrL := thr CcL (le_trans (le_max_left _ _) (le_max_left _ _)) w.length hwN _ hH.2.2.2.2.1
  have hthrN := thr CcN (le_trans (le_max_right _ _) (le_max_left _ _)) N le_rfl _ hH.2.2.2.2.1
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => χ (y / ε)) := hχ.1.comp (contDiff_id.div_const ε)
  set S := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) with hS
  have hS0 : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set B' : Wd.Ix (Fin w.length) → ℝ := fun e => ∑ t, ‖B.hsVec (p.V (B.opApply (Th e t) f) γ)‖ ^ 2 with hB'
  have hB'0 : ∀ e, 0 ≤ B' e := fun e => Finset.sum_nonneg fun t _ => sq_nonneg _
  have hG0 : 0 ≤ G := hG.le
  have key : ∀ e ρ, Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
      ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e (D.cutF p.T.base χ F ε)) γ))‖ ^ 2 ≤
      (((Q e + 1 : ℕ) : ℝ)) ^ 2 * Ke e ^ 2 * Mb e * (G ^ (2 * p₀ - N) * B' e) := by
    intro e ρ
    have hexp := hLe e (fun y => χ (y / ε)) hφ F _ hF hFcc hthrL γ hl hG
    have hc : D.cutF p.T.base χ F ε =
        fun g => (((fun y => χ (y / ε)) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g := rfl
    rw [hc, hexp]
    have ha : ∀ q : Fin (Q e + 1), |(xD^[(q : ℕ)] (fun y => χ (y / ε))) G| ≤ Ke e := by
      intro q
      refine le_trans (hK q ε hε G hG) ?_
      refine le_trans (le_abs_self _) ?_
      exact Finset.single_le_sum (f := fun q : Fin (Q e + 1) => |K q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
    refine le_trans (nf_block (p.TP.E ρ) (fun q : Fin (Q e + 1) => (xD^[(q : ℕ)] (fun y => χ (y / ε))) G) (Ke e) ha
      (fun q => p.V (B.opApply (Lq e q) F) γ) _) ?_
    have hq : ∀ q : Fin (Q e + 1), Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (Lq e q) F) γ))‖ ^ 2 ≤ Mb e * G ^ (2 * p₀ - N) * B' e :=
      fun q => hb e f A₀ hH.2.2.1 hH.2.2.2.1 hthrN hJ q ρ c hl hG
    have hsum := Finset.sum_le_sum fun q (_ : q ∈ (Finset.univ : Finset (Fin (Q e + 1)))) => hq q
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hK2 : 0 ≤ ((Q e + 1 : ℕ) : ℝ) * Ke e ^ 2 := by positivity
    calc ((Q e + 1 : ℕ) : ℝ) * Ke e ^ 2 * ∑ q : Fin (Q e + 1), Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (Lq e q) F) γ))‖ ^ 2
        ≤ ((Q e + 1 : ℕ) : ℝ) * Ke e ^ 2 * (((Q e + 1 : ℕ) : ℝ) * (Mb e * G ^ (2 * p₀ - N) * B' e)) :=
          mul_le_mul_of_nonneg_left hsum hK2
      _ = _ := by ring
  rw [hU Wp Wq P p _ w c hw0 hl hG]
  have hin : ∀ e, 0 ≤ ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
      ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e (D.cutF p.T.base χ F ε)) γ))‖ ^ 2 :=
    fun e => Finset.sum_nonneg fun ρ _ => by positivity
  rw [Real.norm_of_nonneg (mul_nonneg hS0 (Finset.sum_nonneg fun e _ => hin e))]
  have hE : ∀ e t, TBB.Ew p (fun _ => 1) (B.opApply (Th e t) f) (P.r + 1) [] γ =
      S * ‖B.hsVec (p.V (B.opApply (Th e t) f) γ)‖ ^ 2 := fun e t => TBBx2.Tri.Ew_top p _ hl
  have hR : ∑ i : Fin (Fintype.card ι), ‖G‖ ^ (2 * p₀ - N) *
        TBB.Ew p (fun _ => 1) (B.opApply (Th (σ i).1 (σ i).2) f) (P.r + 1) [] γ =
      ∑ e, G ^ (2 * p₀ - N) * (S * B' e) := by
    rw [Equiv.sum_comp σ (fun x : ι => ‖G‖ ^ (2 * p₀ - N) *
      TBB.Ew p (fun _ => 1) (B.opApply (Th x.1 x.2) f) (P.r + 1) [] γ), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hE, Real.norm_of_nonneg hG0, hB', Finset.mul_sum]
  rw [hR]
  have hblock : ∀ e, ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
      ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e (D.cutF p.T.base χ F ε)) γ))‖ ^ 2 ≤
      Cst e * (G ^ (2 * p₀ - N) * B' e) := by
    intro e
    refine le_trans (Finset.sum_le_sum fun ρ _ => key e ρ) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    simp only [hCst, hnT]
    exact le_of_eq (by ring)
  have hGB : ∀ e, 0 ≤ G ^ (2 * p₀ - N) * (S * B' e) := fun e => by have := hB'0 e; positivity
  calc S * ∑ e, ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e (D.cutF p.T.base χ F ε)) γ))‖ ^ 2
      ≤ S * ∑ e, Cst e * (G ^ (2 * p₀ - N) * B' e) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => hblock e) hS0
    _ = ∑ e, Cst e * (G ^ (2 * p₀ - N) * (S * B' e)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
    _ ≤ ∑ e, (∑ e', Cst e') * (G ^ (2 * p₀ - N) * (S * B' e)) :=
        Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun e' _ => hCst0 e') (Finset.mem_univ e)) (hGB e)
    _ = (∑ e, Cst e) * ∑ e, G ^ (2 * p₀ - N) * (S * B' e) := by rw [Finset.mul_sum]

theorem nfTopDomAllS_of_cut (hZ : NFDomZero) (hP : NFDomPtwS) (hL : DominatedL2OperatorBound) (hM : NFDomMeas) : NFTopDomAllS := by
  intro Cb
  obtain ⟨C1, C₁, H1⟩ := hP Cb
  obtain ⟨C2, H2⟩ := hL Cb C₁
  obtain ⟨C3, H3⟩ := hM Cb
  refine ⟨max C1 (max C2 C3), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hHS w hw hN
  obtain ⟨hH, hJ, -⟩ := hHS
  have mono : ∀ c, c ≤ max C1 (max C2 C3) → NFHyp Cb c p f A₀ p₀ χ N := fun c hc => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
    refine ⟨a1, a2, a3, a4, le_trans ?_ a5, a6⟩
    have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
      positivity
    have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
        x * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
      fun x => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hc hX
  obtain ⟨m, Th, Mb, hMb, hok, hb⟩ := H1 Wp Wq P p p₀ χ Y N w hw hN
  have hb := hb f A₀ (mono C1 (le_max_left _ _)) hJ
  refine ⟨eventually_nhdsWithin_of_forall fun ε hε =>
      H3 Wp Wq P p f A₀ p₀ χ Y N (mono C3 (le_trans (le_max_right _ _) (le_max_right _ _))) w hw hN ε hε,
    fun c => Mb * ∑ t, ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
      TBB.Ew p (fun _ => 1) (B.opApply (Th t) f) (P.r + 1) [] (TBB.bigPt P.r c), ?_, ?_⟩
  · exact (integrable_finsetSum Finset.univ fun t _ =>
      H2 Wp Wq P p f A₀ p₀ χ N (mono C2 (le_trans (le_max_left _ _) (le_max_right _ _))) (Th t) (hok t)).const_mul Mb
  · refine eventually_nhdsWithin_of_forall fun ε hε => ae_of_all _ fun c => ?_
    by_cases hc : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · exact hb ε hε c hc.1 hc.2
    · rw [hZ Wp Wq P p _ w c hc, norm_zero]
      exact mul_nonneg hMb (Finset.sum_nonneg fun t _ =>
        mul_nonneg (pow_nonneg (norm_nonneg _) _) (TBBx4.ew_nonneg p _ _))

theorem nfApxDomAllS_of_cut (hZ : NFDomZero) (hP : NFDomPtwS) (hU : DominatedL2TruncationBound) : NFApxDomAllS := by
  intro Cb
  obtain ⟨C1, C₁, H1⟩ := hP Cb
  obtain ⟨C2, H2⟩ := hU Cb C₁
  refine ⟨max C1 C2 + 1, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hHS w hw hN ε hε
  obtain ⟨hH, -, hJn⟩ := hHS
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
  · exact le_trans (hb (fun g => cutN P.k P.r n g • f g) (A₀ - 1) (hyp C1 (le_max_left _ _) n) (hJn n) ε hε c hc'.1 hc'.2)
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => (hc t).trans (le_abs_self _)) hMb)
  · rw [hZ Wp Wq P p _ w c hc', norm_zero]
    exact mul_nonneg hMb (Finset.sum_nonneg fun t _ => abs_nonneg _)

theorem nfDomPtwS_of_open (hL : NFLeibV) (hN : NFCoreNS) : NFDomPtwS :=
  nfDomPtwS_of_cut unfolding_top_term_holds vector_multiplication_holds truncated_supremum_bound_holds hL hN empty_operator_list_holds

end

end Formalism.FourierDecayAlt.P.CutBP
