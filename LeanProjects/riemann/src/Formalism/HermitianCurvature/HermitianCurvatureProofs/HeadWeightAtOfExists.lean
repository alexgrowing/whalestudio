import Formalism.HermitianCurvature.HermitianCurvatureProofs.CastVMulVecLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DetCornerMatrixLevelZero

open Matrix MeasureTheory Finset
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF

theorem interp_any {ι : Type} [Fintype ι] (node : ι → ℂ) (hinj : Function.Injective node) (f : ι → ℂ) :
    ∃ q : Polynomial ℂ, ∀ i, q.eval (node i) = f i := by
  classical
  refine ⟨Lagrange.interpolate Finset.univ node f, fun i => ?_⟩
  exact Lagrange.eval_interpolate_at_node f hinj.injOn (Finset.mem_univ i)

section frame

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem frame_dframe (S : B.RealPlaceData k r Wp Wq) (hr : r = 0) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ γ : B.Mat k r}
    (hD : D.IsDFrame S ν' m₀ γ) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs) :
    Q.IsFrameOf k r [γ⁻¹ *ᵥ S.z, S.z'] Bs := by
  subst hr
  obtain ⟨hB1, hB2, hB3⟩ := hB
  refine ⟨hB1, hB2, fun a v hv => ?_⟩
  simp only [List.mem_cons, List.mem_singleton] at hv
  rcases hv with rfl | rfl | hv
  · obtain ⟨-, ⟨α, -, hα⟩, -⟩ := hD
    have hcof : Formalism.FourierDecayAlt.D.cofL S γ = S.z := by
      unfold Formalism.FourierDecayAlt.D.cofL
      simp [Matrix.adjugate_fin_one, fvec, Matrix.one_apply]
    rw [hcof] at hα
    have hvb : (fun i : Fin (2 * 0 + k + 1) => if 0 ≤ i.val ∧ i.val ≤ 0 + k then (γ⁻¹ *ᵥ S.z) i else 0) =
        γ⁻¹ *ᵥ S.z := by
      funext i
      have := i.isLt
      rw [if_pos (by omega)]
    have hpr : γ⁻¹ *ᵥ S.z = Formalism.FourierDecayAlt.D.prW k 0 S.z' (γ⁻¹ *ᵥ S.z) +
        (herm (Hpk k 0) (γ⁻¹ *ᵥ S.z) S.z' / herm (Hpk k 0) S.z' S.z') • S.z' := by
      unfold Formalism.FourierDecayAlt.D.prW
      dsimp only
      rw [hvb, sub_add_cancel]
    have h1 : herm (Hpk k 0) (Bs a) ν' = 0 := hB3 a ν' (by simp)
    have h2 : herm (Hpk k 0) (Bs a) S.z' = 0 := hB3 a S.z' (by simp)
    rw [hpr, hα]
    unfold herm at h1 h2 ⊢
    rw [star_add, star_smul, star_smul, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2, smul_zero,
      smul_zero, add_zero]
  · exact hB3 a S.z' (by simp)
  · simp at hv

end frame

def HeadWeightAtOfEx : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.CutWord P p.l0 w → PBI.LevFrame p ν'r m₀r →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∀ γ₀ ∈ B.GV P.k (P.r - P.r),
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 →
      D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀ →
    (∀ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        ∑ ρ : M.Ty P, (p.TP.E ρ).comp ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) =
          (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) →
    (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (p.TP.E ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀))

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexOrder

theorem head_weight_at_of_exists : DiagonalScalarMatrices.HeadWeightAtOfEx := by
  intro Wp Wq _ _ _ _ _ _ P p w X μ L st ν'r m₀r hD hcut hLF x hx γ₀ hγG hζ hγF hex h hh y e
  obtain ⟨hl1, hlk, hk2⟩ := p.hl
  have hr : P.r - P.r = 0 := by omega
  have hD' := hD
  obtain ⟨hPl, -, -, -, hq, hinv, -, -⟩ := hD'
  have hOK := hPl.1

  have hw := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P P.r) _ _ _ _ st p.l0 hOK hl1 hlk hq hinv w hcut.1 hcut.2

  have hGx : 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' := hx.2.2
  have hx' : (x.1, γ₀) ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := by
    refine ⟨hx.1, ⟨hγG, fun a ha => by
      exfalso; have h1 := a.isLt; have h2 : (JC.parLev P P.r).r = P.r - P.r := rfl; omega⟩, ?_⟩
    show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
    rw [hζ]; exact hGx

  have hbase := hLF.2.2
  obtain ⟨hν, hνz, hνν, -, -⟩ := id hbase
  obtain ⟨Bs', hB'⟩ := Formalism.FourierDecayAlt.P.Topx1.vecw_frame_exists P.k (P.r - P.r) (by omega) (p.T.bs P.r).z' ν'r
    (p.T.bs P.r).z'_mem (p.T.bs P.r).T'_pos hν hνz hνν
  have hBγ := DiagonalScalarMatrices.frame_dframe (p.T.bs P.r) hr hγF hB'

  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  set f : M.Ty P → ℂ := fun ρ => Fr.cs (M.x0 P p.l0 ρ) (M.qC P) (D.positionted w) e with hfdef
  obtain ⟨q, hq'⟩ := DiagonalScalarMatrices.interp_any (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) hY₀ f
  set V := ((y e : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
    (p.T.bs P.r).π (p.T.bs P.r).π') : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ with hVdef
  have hV := PBI.grpInt_at_dframe p hLF (y e) x hx hγG hζ hγF
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 := DiagonalScalarMatrices.dw_pt (JC.parLev P P.r) _ _ _ _ X μ L st p.l0 hD (D.positionted w) hw Y₀ e q hq' y x.1 γ₀ hx' Bs' hBγ v
  have h2 := DiagonalScalarMatrices.poly_types p ν'r m₀r hLF hB' V hV (hex (y e)) (Y₀ : ℂ) q v
  rw [show ((JC.parLev P P.r).k : ℂ) = (P.k : ℂ) from rfl, ← hVdef] at h1
  erw [h2] at h1
  rw [h1]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  rw [hq' ρ]
  set ζx := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζx
  have hTb : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
  have hTb' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
  have hTr : Tz P.k (P.r - P.r) (p.T.bs P.r).z = P.T := hPl.2.2.2.1
  have hTr' : Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T' := hPl.2.2.2.2.1
  have hzγ : Q.zetaL (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (Fin.last (JC.parLev P P.r).r) γ₀ = ζx := hζ
  have hGG : Q.GGl (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ =
      Complex.normSq ζx - P.T * P.T' := by
    show Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' = _
    rw [hζ, hTr, hTr']
  have hG0 : 0 < Complex.normSq ζx - P.T * P.T' := by rw [← hTr, ← hTr']; exact hGx
  have hlen : (D.positionted w).length = w.length := List.length_ofFn
  have hcW : Top.cW P p.l0 w e ρ = f ρ := by
    simp only [Top.cW, hfdef]
    congr 1
  have hc := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
    Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true (Fin w.length) P.k P.u P.u' (M.rho P ρ) p.l0 P.T P.T'
    (D.positionted w) hl1 hlk (Formalism.FourierDecayAlt.P.types_interlace P p.hP.1 ρ) p.hP.1.T_pos p.hP.1.T'_pos hw.2.1 hw.2.2 e
  have hpos : 0 < f ρ := by rw [Complex.lt_def]; exact ⟨hc.1, hc.2.symm⟩
  have hre : 0 < (f ρ).re := (Complex.lt_def.1 hpos).1
  have him : (f ρ).im = 0 := (Complex.lt_def.1 hpos).2.symm
  have hfre : f ρ = ((f ρ).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hW := PBI.wPt_app (P.T * P.T') ζx h P.r hh
  have hWnn : 0 ≤ Top.wPt (P.T * P.T') P.r (h ++ [(1, ζx)]) := by
    rw [hW]; exact div_nonneg (Complex.normSq_nonneg _) hG0.le
  unfold Top.dH
  rw [hTb, hTb', hW, hcW, Real.sq_sqrt (mul_nonneg (pow_nonneg (by rw [← hW]; exact hWnn) _) hre.le), hGG, hzγ, hlen]
  rw [hfre]
  push_cast
  rw [div_eq_mul_inv, Complex.ofReal_re]

end Formalism.FourierDecayAlt.P
