import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec

noncomputable section

namespace GlobalTheory.BigRec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem pnorm_pos_of_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (P : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have := (hx τ).2 i
    rw [h0] at this
    simp at this
  refine mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_)
  exact Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _

theorem exp_le_of_neg_log_sqrt_le {S a b : ℝ} (hS : 0 < S) (h : -Real.log (Real.sqrt S) ≤ a + b) :
    Real.exp (-(2 * b)) ≤ Real.exp (2 * a) * S := by
  rw [Real.log_sqrt hS.le] at h
  calc Real.exp (-(2 * b)) ≤ Real.exp (2 * a + Real.log S) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (2 * a) * S := by rw [Real.exp_add, Real.exp_log hS]

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_rdU_ne_zero {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) {N : ℕ} (w : Fin N → Rul Xo c)
    (hw : NoCommonZero Xo c w) (k : U.Comp) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ∃ m, rdU U (w m) k x ≠ 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨m, hm⟩ := hw (CAt σ) (U.un k ⟨x, hx⟩)
  refine ⟨m, ?_⟩
  have e : rdU U (w m) k x = toC (evR Xo c (w m) (U.un k ⟨x, hx⟩)) := dif_pos hx
  rw [e]
  exact hm

theorem model_ineq_of_log_bound {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (σ : c.F →+* ℂ)
    {N N' : ℕ} (i : ℕ) (w : Fin N → Rul Xo c) (e : Fin (N' + 1) ≃ Fin N) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (th tableLineDegreeFive DF tableLineDegreeTwo cc : ℝ) (hσ : GoodEmb c σ)
    (hI : I2AtFramePoints U xR (fun m => w (e m)) (a, n) th tableLineDegreeFive DF cc) (hw : NoCommonZero Xo c w)
    (k : (U σ).Comp) (eW : ReciprocityTheory.ChartRestriction.G.FD.Wt ((U σ).X k).Ψ r)
    (et : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r → ℂ)
    (het : ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm eW et x ≤
      Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x - tableLineDegreeTwo))) :
    ReciprocityTheory.ChartRestriction.G.AR.Up.InterpolationModelInequalities ((U σ).X k) (laU (U σ) a n k) eW (fun m => rdU (U σ) (w m) k) et cc i
      (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th) := by
  refine ⟨⟨Real.exp (2 * (tableLineDegreeFive * DF)) * lieFac Dw xR a ^ 2, fun x hx => ?_⟩,
    Real.exp (2 * (i * tableLineDegreeTwo)), fun x hx => ?_⟩
  · have h1 := hI σ hσ k x hx
    have hs : ∑ m, recNrm (U σ) xR a n (w (e m)) k x ^ 2 =
        lieFac Dw xR a ^ 2 * ∑ m, ((U σ).X k).pnorm (laU (U σ) a n k) (rdU (U σ) (w m) k) x ^ 2 := by
      rw [Finset.mul_sum, ← e.sum_comp]
      exact Finset.sum_congr rfl fun m _ => by rw [recNrm, mul_pow]
    have hpos : 0 < ∑ m, ((U σ).X k).pnorm (laU (U σ) a n k) (rdU (U σ) (w m) k) x ^ 2 := by
      obtain ⟨m, hm⟩ := exists_rdU_ne_zero (U σ) w hw k hx
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨m, Finset.mem_univ _, pow_pos (pnorm_pos_of_ne_zero _ _ _ hx hm) 2⟩
    simp only [hs] at h1
    have h2 := exp_le_of_neg_log_sqrt_le (mul_pos (pow_pos (lieFac_pos Dw xR a) 2) hpos) h1
    rw [← mul_assoc, ← mul_assoc] at h2
    exact h2
  · have h0 : 0 ≤ ((U σ).X k).pnorm eW et x :=
      mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
        Real.rpow_nonneg (norm_nonneg _) _)
    refine (pow_le_pow_left₀ h0 (het x hx) 2).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring

end Gen

theorem firstMin_fn_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (th : ℝ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    0 ≤ ReciprocityTheory.ChartRestriction.G.I2.phiFD X th x := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD
  split_ifs <;> positivity

theorem firstMin_fn_lower {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {th : ℝ} (hth : 0 < th) :
    ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 →
      ca / X.la1 x ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.phiFD X th x := by
  have hf : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    have h1 := IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hrd : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.rd
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))) _
  refine ⟨2 * ReciprocityTheory.ChartRestriction.G.I2.PT.f E / ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2, th, by positivity, hth,
    fun x _ hlt => ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD
  rw [if_pos hlt, div_div]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem phRec_of_firstMin : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (wL : WeightFamilies.Wt D j) (N N' i : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (e : Fin (N' + 1) ≃ Fin N) (et : (recB h.toLawsCore).Cusp j (etWt D j i)) (th tableLineDegreeFive DF tableLineDegreeTwo c : ℝ), GoodEmb T.Q.c σ → 0 < th → I2AtFramePoints (T.U j) (xiR D) (fun m => (w (e m)).1) (wtA wL, wL.n) th tableLineDegreeFive DF c → NoCommonZero (T.Q.Xo j) T.Q.c (fun m => (w m).1) → (∀ k : (T.U j σ).Comp, ∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (etWt D j i)) ((etWt D j i)).n k) (rdU (T.U j σ) et.1 k) x ≤ Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x - tableLineDegreeTwo))) → PhRec h j σ w i et c := by
  intro D T h j hj σ wL N N' i w e et th tableLineDegreeFive DF tableLineDegreeTwo c hσ hth hI hw het k
  exact ⟨ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th, fun x _ => firstMin_fn_nonneg _ th x,
    firstMin_fn_lower _ hth,
    model_ineq_of_log_bound (T.U j) (xiR D) σ i (fun m => (w m).1) e (wtA wL) wL.n th tableLineDegreeFive DF tableLineDegreeTwo c hσ hI hw k _ _
      (het k)⟩

end GlobalTheory.BigRec
