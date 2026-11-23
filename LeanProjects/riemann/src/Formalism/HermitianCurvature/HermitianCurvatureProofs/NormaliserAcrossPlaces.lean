import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive

namespace Formalism.FourierDecayAlt.P.CutBP2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section hs

variable {Wp Wq Wq' Wq'' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  [NormedAddCommGroup Wq''] [InnerProductSpace ℂ Wq''] [FiniteDimensional ℂ Wq'']

lemma hs_le_of_adj_sh (X : Wq →L[ℂ] Wp) (A : Wq' →L[ℂ] Wq) (A' : Wq'' →L[ℂ] Wq) (K : ℝ)
    (h : ∀ v : Wq, ‖v‖ ^ 2 ≤
      K * (‖(ContinuousLinearMap.adjoint A) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint A') v‖ ^ 2)) :
    ‖B.hsVec X‖ ^ 2 ≤ K * (‖B.hsVec (X.comp A)‖ ^ 2 + ‖B.hsVec (X.comp A')‖ ^ 2) := by
  rw [Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj X, Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A),
    Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A'), ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  exact h _

lemma hs_comp_le_sh (X : Wq →L[ℂ] Wp) (A : Wq' →L[ℂ] Wq) :
    ‖B.hsVec (X.comp A)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A), Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj X, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  have h1 := (ContinuousLinearMap.adjoint A).le_opNorm
    ((ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j))
  rw [LinearIsometryEquiv.norm_map] at h1
  calc ‖(ContinuousLinearMap.adjoint A) ((ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j))‖ ^ 2
      ≤ (‖A‖ * ‖(ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j)‖) ^ 2 := by gcongr
    _ = ‖A‖ ^ 2 * ‖(ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by ring

end hs

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

lemma ttp_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') : TTp q = TTp p := by
  unfold TTp
  rw [hz, hz']
  rfl

lemma ew_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) :
    Ew q (fun _ => 1) F (P.r + 1) [] γ =
      (Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ)) * ‖B.hsVec (q.V F γ)‖ ^ 2 := by
  have h := Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top q F hγ
  rw [ttp_sh p q hz hz'] at h
  exact h

lemma V_fpmSh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (APt : C.LPt → (Wq' →L[ℂ] Wq)) (p₀ : ℕ)
    (hz : q.T.base.z = p.T.base.z) (hz' : q.T.base.z' = p.T.base.z') {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ)
    (hA : q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (APt γ)) :
    q.V (fpmSh (P := P) q f A p₀) γ = ((Gp p γ ^ p₀ : ℝ) : ℂ) • (p.V f γ).comp (APt γ) := by
  have hGq : Gp q γ = Gp p γ := by
    unfold Gp
    rw [ttp_sh p q hz hz']
    rfl
  have h := Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow q (fun g => (f g).comp (A g)) p₀ hγ (hGq ▸ hG)
  rw [hA, hGq] at h
  exact h

lemma big_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (APt : C.LPt → (Wq' →L[ℂ] Wq)) (n₀ p₀ : ℕ)
    (hz : q.T.base.z = p.T.base.z) (hz' : q.T.base.z' = p.T.base.z')
    (hA : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (APt γ))
    (hn : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖APt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀)
    (c : Fin (P.r + 1) → ℂ) :
    Ew q (fun _ => 1) (fpmSh (P := P) q f A p₀) (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c) := by
  set γ := bigPt P.r c with hγdef
  by_cases hloc : D.IsLocPt γ (P.r + 1)
  swap
  · have h0q : Ew q (fun _ => 1) (fpmSh (P := P) q f A p₀) (P.r + 1) [] γ = 0 :=
      Formalism.FourierDecayAlt.P.TBBx4.ew_not_loc q _ hloc
    rw [h0q, Formalism.FourierDecayAlt.P.TBBx4.ew_not_loc p _ hloc, mul_zero]
  have hGq : Gp q γ = Gp p γ := by
    unfold Gp
    rw [ttp_sh p q hz hz']
    rfl
  rw [ew_sh p q hz hz' _ hloc, Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p f hloc]
  set nn := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) with hnn_def
  have hnn : 0 ≤ nn := mul_self_nonneg _
  by_cases hG : 0 < Gp p γ
  · rw [V_fpmSh p q f A APt p₀ hz hz' hloc hG (hA γ hloc hG), Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
    have h1 := hs_comp_le_sh (p.V f γ) (APt γ)
    have h2 := hn γ hloc hG
    set X2 := ‖B.hsVec (p.V f γ)‖ ^ 2 with hX2_def
    have hX2 : 0 ≤ X2 := sq_nonneg _
    have hTT : 0 ≤ TTp p := Formalism.FourierDecayAlt.P.Qx5.place_alt_alt p.hP
    have hGd : Gp p γ ≤ ‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2 := by
      show D.ptG (TTp p) P.r γ ≤ _
      unfold D.ptG
      rw [Complex.normSq_eq_norm_sq]
      have := Complex.normSq_nonneg (D.ptMatN γ P.r).det
      nlinarith
    have hTq : 0 ≤ (Tq p)⁻¹ ^ n₀ := by
      have h3 : 0 ≤ (Gp p γ / Tq p) ^ n₀ := le_trans (sq_nonneg _) h2
      rw [div_pow, div_eq_mul_inv, ← inv_pow] at h3
      exact (mul_nonneg_iff_of_pos_left (pow_pos hG n₀)).mp h3
    calc nn * ((Gp p γ ^ p₀) ^ 2 * ‖B.hsVec ((p.V f γ).comp (APt γ))‖ ^ 2)
        ≤ nn * ((Gp p γ ^ p₀) ^ 2 * (‖APt γ‖ ^ 2 * X2)) := by gcongr
      _ ≤ nn * ((Gp p γ ^ p₀) ^ 2 * ((Gp p γ / Tq p) ^ n₀ * X2)) := by gcongr
      _ = (Gp p γ) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ * (nn * X2) := by
        rw [div_pow]
        ring
      _ ≤ (‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ * (nn * X2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hG.le hGd _) hTq)
          (mul_nonneg hnn hX2)
      _ = _ := by rw [← pow_mul]
  · have hq0 : q.V (fpmSh (P := P) q f A p₀) γ = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dif_neg]
      rintro ⟨-, h⟩
      apply hG
      rw [← hGq]
      exact h
    have hp0 : p.V f γ = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dif_neg]
      rintro ⟨-, h⟩
      exact hG h
    have e1 := Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq 0 (0 : Wq' →L[ℂ] Wp)
    have e2 := Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq 0 (0 : Wq →L[ℂ] Wp)
    simp only [Complex.ofReal_zero, zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul] at e1 e2
    rw [hq0, hp0, e1, e2, mul_zero, mul_zero]

end sh

theorem normaliser_across_places : NormAtShOfAmaps := by
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀
    hz hz' hzm hzm' hA
  obtain ⟨hAp, hAm, hadj, hnp, hnm⟩ := hA
  refine ⟨fun γ hγ hG => ?_, fun c => big_sh p pp f Ap ApPt n₀ p₀ hz hz' hAp hnp c,
    fun c => big_sh p pm f Am AmPt n₀ p₀ hzm hzm' hAm hnm c⟩
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p f hγ, ew_sh p pp hz hz' _ hγ, ew_sh p pm hzm hzm' _ hγ,
    V_fpmSh p pp f Ap ApPt p₀ hz hz' hγ hG (hAp γ hγ hG),
    V_fpmSh p pm f Am AmPt p₀ hzm hzm' hγ hG (hAm γ hγ hG),
    Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
  have hX := hs_le_of_adj_sh (p.V f γ) (ApPt γ) (AmPt γ)
    ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀) (hadj γ hγ hG)
  set nn := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) with hnn_def
  set a1 := ‖B.hsVec ((p.V f γ).comp (ApPt γ))‖ ^ 2 with ha1
  set a2 := ‖B.hsVec ((p.V f γ).comp (AmPt γ))‖ ^ 2 with ha2
  have hnn : 0 ≤ nn := mul_self_nonneg _
  have hcanc : (Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm p₀ 2, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hG.ne')]
  have e : (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
      (nn * ((Gp p γ ^ p₀) ^ 2 * a1) + nn * ((Gp p γ ^ p₀) ^ 2 * a2)) =
      nn * ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (a1 + a2)) := by
    rw [show (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
        (nn * ((Gp p γ ^ p₀) ^ 2 * a1) + nn * ((Gp p γ ^ p₀) ^ 2 * a2)) =
        nn * ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (a1 + a2)) *
          ((Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2) by ring, hcanc, mul_one]
  rw [e]
  exact mul_le_mul_of_nonneg_left hX hnn

end

end Formalism.FourierDecayAlt.P.CutBP2
