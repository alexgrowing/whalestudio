import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVrad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

section Pic

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem JF_mul_inv (Bs : B.RealPlaceData k r Wp Wq) (m : B.Mat k r → ℂ)
    (hm : ∀ p : B.SS k r, Bs.inSS p → ∀ g, m (B.sgs p g) = m g) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (h : B.Mat k r) : B.JF Bs (fun g => m g • F g) h = m h • B.JF Bs F h := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun g => m g • F g) h ∂Bs.μSS = m h • ∫ p, JF.xiP Bs p • B.rho Bs p F h ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hm p hp h]
  exact smul_comm _ _ _

theorem JF_uInv (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) {h : B.Mat k r} (hh : h ∈ JF.Om k r Bs.z Bs.z') :
    ∀ (w : List C.Letter) (x : Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)), (∀ e, JC.NiceCoef Bs ε (x e)) →
      ∀ e, B.JF Bs (KB.uInv s w x e) h = KB.uInv s w (fun e => B.JF Bs (x e) h) e
  | [], x, _, e => rfl
  | l :: w, x, hx, e => by
    rw [uInv_cons, uInv_cons]
    by_cases h0 : e 0 = 0
    · rw [if_pos h0, if_pos h0]
      exact JF_uInv Bs ε s hh w _ (fun e' => hx _) _
    · rw [if_neg h0, if_neg h0]
      generalize (if l.1 = true then s else (starRingEnd ℂ) s) = c
      have h1 := uInv_nice Bs ε s w (fun e' => x (Fin.cons 1 e')) (fun e' => hx _) (fun a => e a.succ)
      have h2 := uInv_nice Bs ε s w (fun e' => x (Fin.cons 0 e')) (fun e' => hx _) (fun a => e a.succ)
      have e1 := JCx2.bc_JF_add h1 (JCx2.mn_nice_smul c h2) hh
      calc B.JF Bs ((KB.uInv s w (fun e' => x (Fin.cons 1 e')) fun a => e a.succ) +
            c • (KB.uInv s w (fun e' => x (Fin.cons 0 e')) fun a => e a.succ)) h
          = B.JF Bs (fun g => (KB.uInv s w (fun e' => x (Fin.cons 1 e')) fun a => e a.succ) g +
            (fun g => c • (KB.uInv s w (fun e' => x (Fin.cons 0 e')) fun a => e a.succ) g) g) h := rfl
        _ = _ := e1
        _ = _ := by
          rw [JCx2.bc_JF_smul, JF_uInv Bs ε s hh w _ (fun e' => hx _), JF_uInv Bs ε s hh w _ (fun e' => hx _)]

end Pic

section Minor

variable {k r : ℕ}

theorem first_minor_cell_eq_coord {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hr : 0 < r)
    (c : Fin r → ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (h1 : 1 < r + 2) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, h1⟩ = c ⟨0, hr⟩ := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * B2.embWb k r μ = bigCell k r c μ := by
    rw [Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  rw [e]
  have hmin := (big_cell_minors_holds k r z z' c μ hz hz').1 ⟨1, by omega⟩
  have hl : (⟨(⟨1, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = ⟨1, h1⟩ := Fin.ext rfl
  rw [hl] at hmin
  rw [hmin]
  have hs : (Finset.univ.filter fun a : Fin r => a.val < (⟨1, by omega⟩ : Fin (r + 1)).val) = {⟨0, hr⟩} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ha; exact Fin.ext (by simp at ha; omega)
    · rintro rfl; simp
  rw [Finset.prod_filter, ← Finset.prod_filter, hs, Finset.prod_singleton]

theorem first_minor_top_eq_zeta {z z' : Fin (2 * r + k + 1) → ℂ} (hr : r = 0) (c : Fin r → ℂ) (g : Mx k r) (h1 : 1 < r + 2) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, h1⟩ = P5.zeta k r z z' g := by
  subst hr
  have hw : wCell k 0 (Fin.last 0) c = 1 := Formalism.FourierDecayAlt.P.Qx6.wCell_zero c
  rw [hw, one_mul, dmin_one]
  simp [P5.zeta, zetaL, fvec]

end Minor

section Rad

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem radPic_wave (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (w : List C.Letter)
    (x : Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e))
    (Φ : Ix (Fin w.length) → RadSp k r Bs.z Bs.z' Bs.π Bs.π')
    (hΦ : ∀ e, ∀ y ∈ DomR k r Bs.z Bs.z',
      (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF Bs (x e)) y.1 y.2)
    (m : (Fin r → ℂ) → Mx k r → ℂ) (h1 : 1 < r + 2)
    (hm : ∀ y ∈ DomR k r Bs.z Bs.z', m y.1 y.2 = fsv s (Dmin k r Bs.z Bs.z' (wCell k r (Fin.last r) y.1 * y.2) ⟨1, h1⟩))
    (Wv Wv' : Module.End ℂ (RadSp k r Bs.z Bs.z' Bs.π Bs.π')) (hW : multiplicationOperator Wv m) :
    ∀ e, ∀ y ∈ DomR k r Bs.z Bs.z', (act (Vw (mkP Wv Wv') s (D.positionted w)) Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG k r (Fin.last r) (B.JF Bs (KB.waveG Bs s w x e)) y.1 y.2 := by
  intro e y hy
  have hGV : wCell k r (Fin.last r) y.1 * y.2 ∈ B.GV k r := by
    rw [Rad.wCell_last_eq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
  have hh : wCell k r (Fin.last r) y.1 * y.2 ∈ JF.Om k r Bs.z Bs.z' :=
    ⟨hGV, Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hy.1 hy.2.1 hy.2.2⟩
  set h := wCell k r (Fin.last r) y.1 * y.2 with hhdef
  rw [Vw, act_mul, act_io]
  change (Wv (act (UUiw s (D.positionted w)) Φ e) : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = _
  rw [hW, act_UUiw]
  let ev : RadSp k r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
    { toFun := fun Ψ => (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ((KB.uInv s w Φ e : RadSp k r Bs.z Bs.z' Bs.π Bs.π') : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      KB.uInv s w (fun e => (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) e := uInv_map ev s w Φ e
  rw [hev]
  have hfun : (fun e => (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) = fun e => resG k r (Fin.last r) (B.JF Bs (x e)) y.1 y.2 :=
    funext fun e => hΦ e y hy
  rw [hfun]
  simp only [resG]
  set gau : ℂ := ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖y.1 a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ)
    with hgau
  have hsm := uInv_map ((gau • LinearMap.id : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))) s w (fun e => B.JF Bs (x e) h) e
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hsm
  rw [← hsm]
  unfold KB.waveG
  rw [JF_mul_inv Bs (fun g => P5.fsv s (Dmin k r Bs.z Bs.z' g ⟨1, h1⟩))
    (fun p hp g => by rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g]),
    JF_uInv Bs ε s hh w x hx e, hm y hy, smul_comm]

end Rad

end Formalism.FourierDecayAlt.P.PBFV
