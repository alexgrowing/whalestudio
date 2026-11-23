import Formalism.HermitianCurvature.StatementHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransportPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableOfDecay4
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section smul

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_smul' (M : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Wd.Ix S → RadSp k r z z' π π') (a : ℂ) :
    P5.act M (fun e => a • x e) = fun e => a • P5.act M x e := by
  funext e
  simp only [P5.act, map_smul, Finset.smul_sum]

theorem rrform_smul (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (μ : Measure (Mt k r)) (i : Fin (r + 1)) (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ) :
    P5.RRform L st μ i w (fun e => a • x e) (fun e => a • y e) c = a * conj a * P5.RRform L st μ i w x y c := by
  unfold P5.RRform
  rw [act_smul']
  unfold P5.form
  rw [← integral_const_mul]
  congr 1
  funext c'
  simp only [HerA.pairAt_smul_left, HerA.pairAt_smul_right, ← Finset.mul_sum]
  ring

end smul

theorem isLocPt_snoc {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) {t : ℂ} (ht : t ≠ 0) :
    D.IsLocPt (h ++ [(1, t)]) (j + 1) := by
  obtain ⟨h1, h2⟩ := hh
  refine ⟨fun b hb => ?_, ?_⟩
  · rcases List.mem_append.1 hb with hb | hb
    · exact h1 b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact ⟨le_rfl, ht⟩
  · unfold D.ptSize at h2 ⊢
    rw [List.map_append, List.sum_append, h2]
    simp

theorem levW_below (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) {t : ℂ} (ht : t ≠ 0) :
    ‖t‖ ^ (-2 : ℤ) * (‖t‖ ^ (2 * (P.r - j) + P.k)) ^ 2 = KB.levW P (j + 1) t := by
  have hj' : j + 1 ≠ P.r + 1 := by omega
  unfold KB.levW
  rw [if_neg hj']
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
  rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ ht']
  congr 1
  unfold C.Mlev
  push_cast [Nat.cast_sub (show j ≤ P.r by omega)]
  ring

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBP

theorem pb_radHead_of (hOne : PBO.FormOne) (hZN : PBO.ZetaNormExists) (hHP : HeadPic) : KB.RadHead := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' X μ L st Φ Φ' hD hZ hF hw hΦ hΦ' t ht
  let jF : Fin (P.r + 1) := ⟨j + 1, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs p.l0
  obtain ⟨μs, hμs⟩ := hZN P.k (P.r - (j + 1)) Wp Wq (p.T.bs (j + 1))
  have hDs : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' Xs μs Ls sts p.l0 :=
    ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨T, hT, hph⟩ :=
    Formalism.FourierDecayAlt.P.radial_transport_plus Wp Wq P p j hj X μ L st Xs μs Ls sts hD hZ hDs hμs t ht
  refine (hph (Fin w.length) (D.positionted w) Φ Φ' (fun _ => 1) 0).trans ?_
  have hl := isLocPt_snoc hh ht
  have hl' := isLocPt_snoc hh' ht

  set x2 := KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) hl.2 with hx2def
  set x2' := KB.slv p.T F (j + 1) hj w (h' ++ [(1, t)]) hl'.2 with hx2'def
  have hc2 : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl hF e
  have hc2' : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl' hF e
  obtain ⟨ε₁, hε₁, hx⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2
  obtain ⟨ε₂, hε₂, hx'⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2'
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have mono : ∀ {ε' : ℝ} {G : B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)}, min ε₁ ε₂ ≤ ε' →
      JC.NiceCoef (p.T.bs (j + 1)) ε' G → JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) G :=
    fun hle hG => ⟨hG.1, hG.2.1, fun g hg h0 => le_trans hle (hG.2.2 g hg h0)⟩
  have hxn : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2 e) := fun e => mono (min_le_left _ _) (hx e)
  have hxn' : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2' e) := fun e => mono (min_le_right _ _) (hx' e)

  set lam : ℝ := ‖t‖ ^ (2 * (P.r - j) + P.k) with hlam
  have hlam0 : lam ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ht)
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam0
  let b0 : Fin (JC.parLev P j).r := ⟨0, by change 0 < P.r - j; omega⟩
  let Φ2 := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ e)
  let Φ2' := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' e)
  have hpic : ∀ (hh₀ : C.LPt) (hhh : D.IsLocPt hh₀ j) (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
      (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T F j (by omega) w hh₀ hhh.2 e)) →
      ∀ e, ∀ y ∈ Q.DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        Subtype.val ((((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e)) y.1 y.2 =
          Q.resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _)
            (B.JF (p.T.bs jF) (KB.slv p.T F (j + 1) hj w (hh₀ ++ [(1, t)]) (isLocPt_snoc hhh ht).2 e)) y.1 y.2 := by
    intro hh₀ hhh Ψ hΨ e y hy
    have e1 := hT (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e) y.1 y.2
    have e2 := hHP Wp Wq P p F j hj w hh₀ hhh X μ L st Ψ hD hF hw hΨ t (isLocPt_snoc hhh ht) e y hy
    have hcl : ∀ v : Wq →L[ℂ] Wp, ((lam⁻¹ : ℝ) : ℂ) • (((lam : ℝ) : ℂ) • v) = v := fun v => by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0, Complex.ofReal_one, one_smul]
    exact (congrArg (fun v => ((lam⁻¹ : ℝ) : ℂ) • v) (e1.trans e2)).trans (hcl _)
  have hΦ2 := hpic h hh Φ hΦ
  have hΦ2' := hpic h' hh' Φ' hΦ'
  have hOne' := hOne Wp Wq P p.T jF Xs μs Ls sts p.l0 hDs hμs w x2 x2' Φ2 Φ2' (min ε₁ ε₂) hε hxn hxn' hΦ2 hΦ2'
  have hTΦ : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ a)) = fun a => ((lam : ℝ) : ℂ) • Φ2 a := by
    funext a
    simp only [Φ2, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  have hTΦ' : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' a)) = fun a => ((lam : ℝ) : ℂ) • Φ2' a := by
    funext a
    simp only [Φ2', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  rw [hTΦ, hTΦ']
  have hRR : p.RR F (j + 1) w (h ++ [(1, t)]) (h' ++ [(1, t)]) = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := by
    unfold KB.Pl.RR D.RRplace
    rw [dif_pos ⟨hl, hl'⟩, dif_pos hj]
    rfl
  have key : P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := hOne'.symm
  calc _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0) :=
        congrArg _ (rrform_smul Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 (lam : ℂ))
    _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * D.formLev p.T (M.sgn P p.l0) jF w x2 x2') := by
        rw [key]
    _ = _ := by
        rw [hRR, ← levW_below P j hj ht, Complex.conj_ofReal, hlam]
        push_cast
        ring

end Formalism.FourierDecayAlt.P
