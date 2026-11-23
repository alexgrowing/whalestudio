import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

namespace GlobalTheory.HatNF.EmptyWordL2

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem integrable_weight_normSq (hXi : B.XiExists) {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ)
    (hF : ∀ m : ℕ, B.InCC A m F) (hAB : B.AB k r ≤ A) (hT : JF.TransportedAlt k r A 0) :
    Integrable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) := by
  obtain ⟨-, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.BXiAsm.any_of hXi k r Wp Wq D A hAB
  obtain ⟨c4, hc4⟩ := hF 4
  have hfin := (hB1 F F c4 c4 (hF 5) (hF 5) hc4 hc4).1
  have h := Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates k r Wp Wq D A 0 F hT (hF 0)
  have h2 : ContinuousOn (fun q => B.JF D F (B.gq D q)) (Formalism.FourierDecayAlt.P.B7.Q0 D) := h.continuousOn
  have h3 : ContinuousOn (fun q => B.hsVec (B.JF D F (B.gq D q))) (Formalism.FourierDecayAlt.P.B7.Q0 D) :=
    (LinearMap.continuous_of_finiteDimensional
      (⟨⟨B.hsVec, fun X Y => by ext; simp [B.hsVec]⟩, fun a X => by ext; simp [B.hsVec]⟩ :
        (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp))).comp_continuousOn h2
  have hmeas : AEStronglyMeasurable
      (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) volume :=
    Formalism.FourierDecayAlt.P.JCx2.rb_aesm D _ ((Formalism.FourierDecayAlt.P.JCx2.rb_contOn_bcW D).mul (h3.norm.pow 2)) fun q h => by simp [h]
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q =>
    mul_nonneg (Formalism.FourierDecayAlt.P.JCx2.rb_bcWeight_nonneg _ _ q) (sq_nonneg _))]
  exact lt_of_le_of_ne le_top hfin

theorem Ew_bigPt_eq_indicator {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      (Formalism.FourierDecayAlt.P.B7.Q0 p.T.base).indicator
        (fun q => bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q *
          ‖B.hsVec (B.JF p.T.base F (B.gq p.T.base q))‖ ^ 2)
        ((fun j => c j.castSucc), c (Fin.last P.r)) := by
  by_cases hq : ((fun j : Fin P.r => c j.castSucc), c (Fin.last P.r)) ∈ Formalism.FourierDecayAlt.P.B7.Q0 p.T.base
  · rw [Set.indicator_of_mem hq]
    obtain ⟨hc, hlt⟩ := hq
    dsimp only at hc hlt
    have hTT : 0 < Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' := mul_pos p.T.base.T_pos p.T.base.T'_pos
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p F hl, Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt P.k P.r _ _ c hlt.le
    rw [hn, Real.mul_self_sqrt (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _)]
    rfl
  · rw [Set.indicator_of_notMem hq]
    refine Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p F fun h => hq ⟨fun a => ?_, ?_⟩
    · exact (h.1.1 (1, c a.castSucc) (by
        unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a.castSucc, rfl⟩)).2
    · exact Formalism.FourierDecayAlt.P.PBM.zeta_big _ c h.2

end

theorem integrable_density_nil_of_xiExists (hXi : B.XiExists) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) := by
  refine ⟨10, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p H A _ hCC hA
  have ha : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  set x : ℝ := (P.r : ℝ) + 1 with hx
  set n : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hn
  have hx1 : 1 ≤ x := by linarith
  have hn1 : 1 ≤ n := by linarith
  have h1 : x ≤ x ^ 4 := le_self_pow₀ hx1 (by norm_num)
  have h2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have h3 : x * n ^ 2 ≤ x ^ 4 * n ^ 3 := mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 : 10 * (x * n ^ 2) ≤ A := by nlinarith
  have h5 : n ≤ n ^ 2 := le_self_pow₀ hn1 (by norm_num)
  have h6 : x * n ≤ x * n ^ 2 := mul_le_mul_of_nonneg_left h5 (by linarith)
  have h7 : 1 ≤ x * n := by nlinarith
  have hAB : B.AB P.k P.r ≤ A := by
    unfold B.AB
    rw [← hx]
    have : ((P.k : ℝ) + P.r) * x ≤ n * x := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have hT : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    rw [← hx, ← hn]
    nlinarith
  have hint := (integrable_weight_normSq hXi p.T.base H A hCC hAB hT).indicator
    (Formalism.FourierDecayAlt.P.B7.isOpen_good_set p.T.base).measurableSet
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  have h8 := (hmp.integrable_comp_emb e.measurableEmbedding).2 hint
  refine h8.congr (Filter.Eventually.of_forall fun c => ?_)
  simp only [Function.comp]
  rw [he c]
  exact (Ew_bigPt_eq_indicator p H c).symm

theorem integrable_density_nil : GlobalTheory.HCXi.BesselXiIntegrable → ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) :=
  fun h => integrable_density_nil_of_xiExists (GlobalTheory.HCXi.xiExists_of_besselXiIntegrable h)

end GlobalTheory.HatNF.EmptyWordL2
