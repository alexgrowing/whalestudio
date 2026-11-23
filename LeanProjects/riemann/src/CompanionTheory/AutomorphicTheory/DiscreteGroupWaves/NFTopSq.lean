import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCellsOfParts
import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.IntegralEqOfSqrtCauchy

namespace CompanionTheory.NFCpt

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

noncomputable section

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

abbrev SqIx (P : M.Par) (w : List C.Letter) : Type := Option (Wd.Ix (Fin w.length) × M.Ty P)

def sqW (p : KB.Pl P Wp Wq) (w : List C.Letter) (γ : C.LPt) : SqIx P w → ℝ
  | none => if w = [] then Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) else 0
  | some q => if w = [] then 0 else
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Top.dH P p.l0 (TBB.TTp p) w γ q.1 q.2

def sqX (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    SqIx P w → (Wq →L[ℂ] Wp)
  | none => p.V H γ
  | some q => (p.TP.E q.2).comp (p.V (p.Θ.Θ w q.1 H) γ)

theorem hsInner_self_re (A : Wq →L[ℂ] Wp) : (B.hsInner A A).re = ‖B.hsVec A‖ ^ 2 := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  norm_cast

theorem V_of_not (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : ¬ D.IsLocPt γ (P.r + 1)) : p.V H γ = 0 := by
  unfold KB.Pl.V D.vecV
  rw [dif_neg fun h => hγ h.1]

theorem ew_top_eq (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    TBB.Ew p (fun _ => 1) H (P.r + 1) w γ = ∑ i : SqIx P w, sqW p w γ i ^ 2 * ‖B.hsVec (sqX p H w γ i)‖ ^ 2 := by
  have hn : TBB.normC (fun _ => (1 : ℝ)) w = 1 := by simp [TBB.normC]
  unfold TBB.Ew TBB.NP
  rw [Complex.re_ofReal_mul, hn, div_one, Fintype.sum_option]
  by_cases hγ : D.IsLocPt γ (P.r + 1)
  · unfold KB.Pl.RR D.RRplace
    rw [dif_pos ⟨hγ, hγ⟩, dif_neg (by omega), if_pos rfl]
    by_cases hw : w = []
    · rw [if_pos hw, hsInner_self_re]
      simp only [sqW, sqX, if_pos hw, KB.Pl.V]
      simp [sq]
    · rw [if_neg hw]
      unfold Top.topOf
      simp only [sqW, sqX, if_neg hw, KB.Pl.V, Complex.re_sum, Complex.re_ofReal_mul, hsInner_self_re,
        Fintype.sum_prod_type, Finset.mul_sum, TBB.TTp]
      rw [show (0 : ℝ) ^ 2 * ‖B.hsVec (D.vecV p.T.base p.ν' p.m₀ H γ)‖ ^ 2 = 0 by simp, zero_add]
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
      ring
  · have h0 : p.RR H (P.r + 1) w γ γ = 0 := by
      unfold KB.Pl.RR D.RRplace
      rw [dif_neg fun h => hγ h.1]
    rw [h0]
    simp [sqX, V_of_not p _ hγ, JCx1.needs.hsVec_zero]

theorem ew_top_nonneg (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    0 ≤ TBB.Ew p (fun _ => 1) H (P.r + 1) w γ := by
  rw [ew_top_eq]
  positivity

theorem sqX_sub (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {w : List C.Letter}
    (hw : KB.CutWord P p.l0 w) {H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef p.T.base H₁)
    (h₂ : KB.CptCoef p.T.base H₂) (γ : C.LPt) (i : SqIx P w) :
    sqX p (fun g => H₁ g - H₂ g) w γ i = sqX p H₁ w γ i - sqX p H₂ w γ i := by
  cases i with
  | none => exact PBN.vecV_sub _ _ _ _ h₁ h₂
  | some q =>
    obtain ⟨F₁, hF₁, hΘ₁, hV₁⟩ := theta_compact_support Wp Wq P p H₁ w q.1 Cb hCb h₁ hw
    obtain ⟨F₂, hF₂, hΘ₂, hV₂⟩ := theta_compact_support Wp Wq P p H₂ w q.1 Cb hCb h₂ hw
    obtain ⟨nf, fib, o, κ, Dop, -, hIn, -, -, hΘ⟩ := hCb w hw q.1
    have hlen : ∀ T ∈ Dop, T.word.length ≤ o := by
      intro T hT
      obtain ⟨_, _, _, _, _, _, _, hl, _⟩ := hIn.2.2 T hT
      omega
    have e : p.V (p.Θ.Θ w q.1 (fun g => H₁ g - H₂ g)) γ = p.V (fun g => F₁ g - F₂ g) γ := by
      refine PBE.vecV_congrGPos _ _ _ _ fun g hg => ?_
      have hg' : g ∈ C6.domL p.T.base ∅ := ⟨hg.1, hg.2, fun l hl => by simp at hl⟩
      rw [← hΘ₁ g hg', ← hΘ₂ g hg', hΘ _ g hg', hΘ _ g hg', hΘ _ g hg']
      exact PBE.opApply_subGV Dop hlen (B5.ckOn_mono le_top h₁.1) (B5.ckOn_mono le_top h₂.1) g hg.1
    simp only [sqX]
    rw [e, hV₁, hV₂, ← ContinuousLinearMap.comp_sub]
    congr 1
    exact PBN.vecV_sub _ _ _ _ hF₁ hF₂

theorem sqrt_sum_tri {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ι → ℝ)
    (x y : ι → E) :
    |Real.sqrt (∑ i, a i ^ 2 * ‖x i‖ ^ 2) - Real.sqrt (∑ i, a i ^ 2 * ‖y i‖ ^ 2)| ≤
      Real.sqrt (∑ i, a i ^ 2 * ‖x i - y i‖ ^ 2) := by
  have key : ∀ z : ι → E, Real.sqrt (∑ i, a i ^ 2 * ‖z i‖ ^ 2) =
      ‖(WithLp.toLp 2 fun i => (a i : ℂ) • z i : PiLp 2 fun _ : ι => E)‖ := by
    intro z
    rw [PiLp.norm_eq_of_L2]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [norm_smul, mul_pow]
  rw [key, key, key (fun i => x i - y i)]
  refine (abs_norm_sub_norm_le _ _).trans (le_of_eq ?_)
  congr 1
  ext i
  simp [smul_sub]

theorem topD_tri (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {w : List C.Letter}
    (hw : KB.CutWord P p.l0 w) {H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef p.T.base H₁)
    (h₂ : KB.CptCoef p.T.base H₂) (c : Fin (P.r + 1) → ℂ) :
    |Real.sqrt (topD p H₁ w c) - Real.sqrt (topD p H₂ w c)| ≤ Real.sqrt (topD p (fun g => H₁ g - H₂ g) w c) := by
  unfold topD
  rw [ew_top_eq, ew_top_eq, ew_top_eq]
  refine (sqrt_sum_tri _ _ _).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sqX_sub p hCb hw h₁ h₂]
  congr 3

theorem V_bigPt_aesm (p : KB.Pl P Wp Wq) {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hH : KB.CptCoef p.T.base H) :
    AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) volume := by
  obtain ⟨Φ0, hΦ, -, -, hV⟩ := phi_zero_hermitian_curvature Wp Wq P p H hH
  have hcont : Continuous (fun q : (Fin (P.r + 1) → ℂ) × U.XiH (P.r + 1) 0 1 =>
      U.psiH U.betaU 1 q.2 • Φ0 (U.ZjH (p := P.r + 1) (s := 0) 1 q.1 q.2 fun x => x.elim0)) := by
    have hZ : Continuous (fun q : (Fin (P.r + 1) → ℂ) × U.XiH (P.r + 1) 0 1 =>
        U.ZjH (p := P.r + 1) (s := 0) 1 q.1 q.2 fun x => x.elim0) := by
      have e : (fun q : (Fin (P.r + 1) → ℂ) × U.XiH (P.r + 1) 0 1 => U.ZjH (p := P.r + 1) (s := 0) 1 q.1 q.2 fun x => x.elim0) =
          fun q => U.headH 1 q.1 q.2.2.1 q.2.2.2 := funext fun q => PBM.zjH_eq 1 q.1 q.2
      rw [e]
      unfold U.headH
      exact ((continuous_const.matrix_mul ((Dx2.SL.cont_lowW 1).comp continuous_snd.snd.fst)).matrix_mul
        continuous_fst.matrix_diagonal).matrix_mul (Dx2.SL.cont_upper.comp continuous_snd.snd.snd)
    exact ((Ux13.continuous_psiH U.betaU 1).comp continuous_snd).smul (hΦ.continuous.comp hZ)
  have hm : StronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
      U.PhiTop (p := P.r + 1) (s := 0) U.betaU 1 c Φ0 fun x => x.elim0) := by
    unfold U.PhiTop U.muXiH
    exact hcont.stronglyMeasurable.integral_prod_right'
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [ae_coords_ne_zero (P.r + 1)] with c hc
  exact (hV _ 1 c (PBJ.Dens.isLocPt_bigPt c hc) (PBJ.Dens.ptMatN_bigPt c).symm).symm

theorem sqW_meas (p : KB.Pl P Wp Wq) (w : List C.Letter) (i : SqIx P w) :
    Measurable (fun c : Fin (P.r + 1) → ℂ => sqW p w (TBB.bigPt P.r c) i) := by
  have hn : Measurable (fun c : Fin (P.r + 1) → ℂ => TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) := by
    have e : (fun c : Fin (P.r + 1) → ℂ => TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) = fun c =>
        ∏ i : Fin (P.r + 1), (if 1 + (i : ℕ) = P.r + 1 then (Complex.normSq (c (Fin.last P.r)) - TBB.TTp p) ^ (P.k - 1)
          else ‖c i‖ ^ (2 * (C.Mlev P.k P.r (1 + (i : ℕ)) - 2))) := by
      funext c
      unfold TBB.nPt D.ptGG
      rw [ptLast_bigPt]
      unfold TBB.bigPt
      rw [level_product_of_constant_weights]
    rw [e]
    refine Finset.measurable_prod _ fun i _ => ?_
    split_ifs
    · exact ((Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)).sub_const _).pow_const _
    · exact (measurable_pi_apply i).norm.pow_const _
  have hW : Measurable (fun c : Fin (P.r + 1) → ℂ => Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c)) := by
    have e : (fun c : Fin (P.r + 1) → ℂ => Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c)) = fun c =>
        Complex.normSq (∏ i, c i) / (Complex.normSq (∏ i, c i) -
          TBB.TTp p * Complex.normSq (∏ i : Fin P.r, c i.castSucc)) := by
      funext c
      show Top.wPt (TBB.TTp p) P.r (PBJ.bigPt c) = _
      unfold Top.wPt D.ptG
      rw [PBM.ptMatN_bigPt_head, PBJ.Dens.ptMatN_bigPt, PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal]
    rw [e]
    have h1 : Continuous fun c : Fin (P.r + 1) → ℂ => Complex.normSq (∏ i, c i) :=
      Complex.continuous_normSq.comp (continuous_finsetProd _ fun i _ => continuous_apply i)
    have h2 : Continuous fun c : Fin (P.r + 1) → ℂ => Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
      Complex.continuous_normSq.comp (continuous_finsetProd _ fun i _ => continuous_apply _)
    exact h1.measurable.div (h1.sub (continuous_const.mul h2)).measurable
  cases i with
  | none =>
    simp only [sqW]
    split_ifs
    · exact hn.sqrt
    · exact measurable_const
  | some q =>
    simp only [sqW]
    split_ifs
    · exact measurable_const
    · unfold Top.dH
      exact hn.sqrt.mul ((hW.pow_const _).mul_const _).sqrt

theorem sqX_aesm (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {w : List C.Letter}
    (hw : KB.CutWord P p.l0 w) {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hH : KB.CptCoef p.T.base H) (i : SqIx P w) :
    AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => sqX p H w (TBB.bigPt P.r c) i) volume := by
  cases i with
  | none => exact V_bigPt_aesm p hH
  | some q =>
    obtain ⟨F, hF, -, hV⟩ := theta_compact_support Wp Wq P p H w q.1 Cb hCb hH hw
    simp only [sqX, hV]
    exact (continuous_const.clm_comp continuous_id).comp_aestronglyMeasurable (V_bigPt_aesm p hF)

theorem topD_aesm (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {w : List C.Letter}
    (hw : KB.CutWord P p.l0 w) {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hH : KB.CptCoef p.T.base H) :
    AEStronglyMeasurable (topD p H w) volume := by
  have e : topD p H w = fun c => ∑ i : SqIx P w, sqW p w (TBB.bigPt P.r c) i ^ 2 *
      ‖B.hsVec (sqX p H w (TBB.bigPt P.r c) i)‖ ^ 2 := funext fun c => ew_top_eq p H w _
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact ((sqW_meas p w i).pow_const 2).aestronglyMeasurable.mul
    ((BetaSesquilinearity.hsVec_cont.comp_aestronglyMeasurable (sqX_aesm p hCb hw hH i)).norm.pow 2)

end

end CompanionTheory.NFCpt
