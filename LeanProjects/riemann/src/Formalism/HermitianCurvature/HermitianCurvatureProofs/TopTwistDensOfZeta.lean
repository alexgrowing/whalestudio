import Formalism.HermitianCurvature.TopEntryWaveEquation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfWaveQQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvSelf

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

section Entries

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem zeta_entries (hZ : NF.ActualZetaSmooth) {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ}
    {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} (hP : IsPlace P z z' π π')
    (X : ActualOps P.k P.r z z' π π') (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hQQ : ∀ Y, st.QQ Y = M.sgn P l0 • X.QQ Y) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g))) :
    (∀ Y, mkP Wv' Wv * st.QQ Y 1 1 * mkP Wv Wv' = st.QQ Y 1 1) ∧
    (∀ Y, mkP Wv' Wv * st.QQ Y 1 0 * mkP Wv Wv' = st.QQ Y 1 0 - st.QQ Y 1 1 * algebraMap ℂ _ s) := by

  have hmz : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (m : ℂ → ℂ),
      multiplicationOperator W (fun _ g => m (zeta P.k P.r z z' g)) → NF.IsMulZ W m := by
    intro W m hWm Φ
    obtain ⟨h0, -, -⟩ := Φ.2
    funext c g
    rw [hWm Φ c g]
    show _ = (Q.DomR P.k P.r z z').indicator
      (fun x => m (Q.zetaL P.k P.r z z' (Fin.last P.r) x.2) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) (c, g)
    by_cases hx : (c, g) ∈ Q.DomR P.k P.r z z'
    · rw [Set.indicator_of_mem hx]
      rfl
    · have hz : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 := h0 (c, g) hx
      simp [Set.indicator_apply, hx, hz]

  have hfun : (fun ζ : ℂ => fsv s ζ) =
      (fun y : ℂ => Complex.exp (s * id y - conj s * Complex.conjCLE y)) := funext fun y => rfl
  have hfun2 : (fun ζ : ℂ => Complex.exp (s * ζ - conj s * conj ζ)) =
      (fun y : ℂ => Complex.exp (s * id y - conj s * Complex.conjCLE y)) := funext fun y => rfl
  have hder : ∀ ζ : ℂ, HasFDerivAt (fun y : ℂ => Complex.exp (s * id y - conj s * Complex.conjCLE y))
      (Complex.exp (s * id ζ - conj s * Complex.conjCLE ζ) •
        (s • ContinuousLinearMap.id ℝ ℂ - conj s • (Complex.conjCLE : ℂ →L[ℝ] ℂ))) ζ := fun ζ =>
    (((hasFDerivAt_id ζ).const_mul s).sub ((Complex.conjCLE.hasFDerivAt).const_mul (conj s))).cexp
  have hv1 : ∀ ζ : ℂ, fderiv ℝ (fun y : ℂ => Complex.exp (s * y - conj s * conj y)) ζ 1 =
      Complex.exp (s * ζ - conj s * conj ζ) * (s - conj s) := by
    intro ζ
    rw [hfun2, (hder ζ).fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id',
        id_eq, Complex.conjCLE_apply, map_one, Complex.conj_I, smul_eq_mul, ContinuousLinearMap.coe_coe,
        ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
    ring
  have hvI : ∀ ζ : ℂ, fderiv ℝ (fun y : ℂ => Complex.exp (s * y - conj s * conj y)) ζ Complex.I =
      Complex.exp (s * ζ - conj s * conj ζ) * ((s + conj s) * Complex.I) := by
    intro ζ
    rw [hfun2, (hder ζ).fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id',
        id_eq, Complex.conjCLE_apply, map_one, Complex.conj_I, smul_eq_mul, ContinuousLinearMap.coe_coe,
        ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
    ring
  have hdZ : ∀ ζ, NF.dZ (fun ζ : ℂ => fsv s ζ) ζ = s * fsv s ζ := by
    intro ζ
    unfold NF.dZ fsv
    rw [hv1, hvI]
    linear_combination (-(1 / 2 : ℂ) * Complex.exp (s * ζ - conj s * conj ζ) * (s + conj s)) * Complex.I_sq
  have hdZb : ∀ ζ, NF.dZb (fun ζ : ℂ => fsv s ζ) ζ = -conj s * fsv s ζ := by
    intro ζ
    unfold NF.dZb fsv
    rw [hv1, hvI]
    linear_combination ((1 / 2 : ℂ) * Complex.exp (s * ζ - conj s * conj ζ) * (s + conj s)) * Complex.I_sq
  have hsm : ∀ (c : ℂ) (m : ℂ → ℂ), (∀ ζ, m ζ = c * fsv s ζ) →
      multiplicationOperator (c • Wv) (fun _ g => m (zeta P.k P.r z z' g)) := by
    intro c m hm Φ c' g
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hW Φ c' g, smul_smul, hm]
  have hA : ∀ Y, X.t Y 1 0 * Wv = Wv * X.t Y 1 0 - (s • Wv) * X.t Y 1 1 ∧
      X.t Y 1 1 * Wv = Wv * X.t Y 1 1 ∧
      X.t Y 0 1 * Wv = Wv * X.t Y 0 1 + ((-conj s) • Wv) * X.t Y 1 1 := fun Y =>
    hZ Wp Wq P z z' π π' hP X (fun ζ => fsv s ζ)
      (by rw [hfun]; exact ((((contDiff_const.mul contDiff_id).sub
        (contDiff_const.mul Complex.conjCLE.contDiff)).cexp).contDiffOn)) Wv (s • Wv) ((-conj s) • Wv)
      (hmz Wv (fun ζ => fsv s ζ) hW) (hmz _ _ (hsm s _ hdZ)) (hmz _ _ (hsm (-conj s) _ hdZb)) Y

  have hWW : Wv' * Wv = 1 := by
    apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    show ((Wv' (Wv Φ) : RadSp P.k P.r z z' π π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    funext c g
    rw [hW' (Wv Φ) c g, hW Φ c g, smul_smul]
    have h1 : fsv (-s) (zeta P.k P.r z z' g) * fsv s (zeta P.k P.r z z' g) = 1 := by
      unfold fsv
      rw [← Complex.exp_add]
      convert Complex.exp_zero using 2
      rw [map_neg]
      ring
    rw [h1, one_smul]
  have hcore : ∀ A B : Module.End ℂ (RadSp P.k P.r z z' π π'),
      mkP Wv' Wv * mkP A B * mkP Wv Wv' = mkP (Wv' * A * Wv) (Wv' * B * Wv) := by
    intro A B
    apply Prod.ext
    · simp only [pr_mul_fst, mkPair_fst', mul_assoc]
    · apply MulOpposite.unop_injective
      simp only [pr_mul_snd, mkPair_snd', mul_assoc]
  have e11 : ∀ Y, Wv' * X.t Y 1 1 * Wv = X.t Y 1 1 := by
    intro Y
    rw [mul_assoc, (hA Y).2.1, ← mul_assoc, hWW, one_mul]
  have e10 : ∀ Y, Wv' * X.t Y 1 0 * Wv = X.t Y 1 0 - s • X.t Y 1 1 := by
    intro Y
    rw [mul_assoc, (hA Y).1, mul_sub, ← mul_assoc, hWW, one_mul, smul_mul_assoc, mul_smul_comm,
      ← mul_assoc, hWW, one_mul]
  have e01 : ∀ Y, Wv' * X.t Y 0 1 * Wv = X.t Y 0 1 + (-conj s) • X.t Y 1 1 := by
    intro Y
    rw [mul_assoc, (hA Y).2.2, mul_add, ← mul_assoc, hWW, one_mul, smul_mul_assoc, mul_smul_comm,
      ← mul_assoc, hWW, one_mul]
  refine ⟨fun Y => ?_, fun Y => ?_⟩
  · rw [hQQ Y, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [ActualOps.QQ, Matrix.of_apply]
    rw [hcore, e11 Y, e11 (star Y)]
  · rw [hQQ Y, Matrix.smul_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, ← smul_sub]
    congr 1
    simp only [ActualOps.QQ, Matrix.of_apply]
    rw [hcore, e10 Y, e01 (star Y)]
    apply Prod.ext
    · simp only [mkPair_fst', sub_eq_add_neg, pr_add_fst, pr_neg_fst, pr_mul_fst, pr_alg_fst]
      rw [← Algebra.commutes, ← Algebra.smul_def]
    · apply MulOpposite.unop_injective
      simp only [mkPair_snd', sub_eq_add_neg, pr_add_snd, pr_neg_snd, pr_mul_snd, pr_alg_snd]
      rw [← Algebra.smul_def, neg_smul]

end Entries

open TwistedTransfer in

theorem topTwistDensOfZeta : TopTwistDensOfZeta := by
  intro hZ Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 K hD
  obtain ⟨hP, -, hAL, hQQ, -, -, hSL, hLS⟩ := hD
  intro w hw s Wv Wv' hW hW' x y _ _ c _ g
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]
  have f_fi : mkP Wv Wv' * mkP Wv' Wv = 1 := pr_ext (by simpa using hWW') (by simpa using hWW')
  have fi_f : mkP Wv' Wv * mkP Wv Wv' = 1 := pr_ext (by simpa using hW'W) (by simpa using hW'W)
  have hfn : ∀ g ∈ Fr.zfns L, Commute (mkP Wv Wv') g := by
    obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hAL
    have key : ∀ j j' : Fin 6, Commute (mkP Wv Wv') (mkP (X.fn j) (X.fn j')) := by
      intro j j'
      show _ * _ = _ * _
      exact pr_ext (by simpa using mulOp_comm_fn X Wv _ hW j) (by simpa using (mulOp_comm_fn X Wv' _ hW' j').symm)
    intro g hg
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact key _ _
    · rw [hzi]; exact key _ _
    · rw [hzb]; exact key _ _
    · rw [hzbi]; exact key _ _
    · rw [hG]; exact key _ _
    · rw [hGi]; exact key _ _
  have hGG : Commute (mkP Wv Wv') L.GG := hfn _ (mem_zfns L).2.2.2.2.1
  have hfiGG : Commute (mkP Wv' Wv) L.GG := (commute_inv hGG.symm f_fi fi_f).symm
  obtain ⟨e11, e10⟩ := zeta_entries hZ hP X st l0 hQQ s Wv Wv' hW hW'
  have hx : ∀ Y, Commute (mkP Wv Wv') (st.x Y) := by
    intro Y
    have h := e11 Y
    rw [hLS.tau Y] at h
    have h1 : L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv') = L.GG * st.x Y := by
      conv_rhs => rw [← h]
      rw [← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq]
      simp only [mul_assoc]
    have h2 : mkP Wv' Wv * st.x Y * mkP Wv Wv' = st.x Y := by
      calc mkP Wv' Wv * st.x Y * mkP Wv Wv' = L.GGi * (L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv')) := by
            rw [← mul_assoc, L.GGi_GG, one_mul]
        _ = L.GGi * (L.GG * st.x Y) := by rw [h1]
        _ = st.x Y := by rw [← mul_assoc, L.GGi_GG, one_mul]
    show mkP Wv Wv' * st.x Y = st.x Y * mkP Wv Wv'
    calc mkP Wv Wv' * st.x Y = mkP Wv Wv' * (mkP Wv' Wv * st.x Y * mkP Wv Wv') := by rw [h2]
      _ = st.x Y * mkP Wv Wv' := by rw [← mul_assoc, ← mul_assoc, f_fi, one_mul]
  have hl : ∀ Y ∈ st.inv, mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv' =
      L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ _ s := by
    intro Y hY
    have h := e10 Y
    rw [hLS.low Y hY, hLS.tau Y] at h
    have hfix : Commute (mkP Wv' Wv) (st.x Y) := (commute_inv (hx Y).symm f_fi fi_f).symm
    have cancel : ∀ T, st.xi Y * L.GGi * (L.GG * st.x Y * T) = T := by
      intro T
      calc st.xi Y * L.GGi * (L.GG * st.x Y * T) = st.xi Y * (L.GGi * L.GG) * st.x Y * T := by
            simp only [mul_assoc]
        _ = T := by rw [L.GGi_GG, mul_one, (hLS.x_xi Y hY).2, one_mul]
    have h3 : mkP Wv' Wv * (L.GG * st.x Y * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y)) * mkP Wv Wv' =
        L.GG * st.x Y * (mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv') := by
      rw [← mul_assoc (mkP Wv' Wv) (L.GG * st.x Y), ← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq,
        mul_assoc L.GG (mkP Wv' Wv), hfix.eq]
      simp only [mul_assoc]
    rw [h3, ← mul_sub] at h
    rw [← cancel (mkP Wv' Wv * _ * mkP Wv Wv'), h, cancel]
  have hWH : WaveHyp L st (mkP Wv Wv') (mkP Wv' Wv) s := ⟨f_fi, fi_f, rfl, hfn, hx, hl⟩
  obtain ⟨hFV, hd⟩ := frame_twist_F hSL hLS hWH w hw.1
  have hM : (Fr.ofWord L st w).d L * (Fr.ofWord L st w).F * Vw (mkP Wv Wv') s w =
      io (mkP Wv Wv') * ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) := by
    rw [mul_assoc, hFV, ← mul_assoc, ← hd.eq, mul_assoc]
  unfold topDens
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← act_mul, hM, act_mul, act_io, mkPair_fst', hW1, hsInner_smul_left]

end Formalism.FourierDecayAlt.P5
