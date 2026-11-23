import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.BotMulVecExt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix ComplexConjugate

namespace GlobalTheory.RiemMaj

section Core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

noncomputable def pc (x : Frame X.Ψ r) (v : Fin r → E) (t : X.Ψ × Fin r) : ℂ :=
  if (t.2 : ℕ) < X.p0 then hermC t.1.1 X.Gm (col (mat x t.1) t.2) (Data.emb t.1.1 v)
  else ((mat x t.1)⁻¹ *ᵥ Data.emb t.1.1 v) t.2

theorem re_xi (τ : E →+* ℂ) : (τ X.ξ0).re = 0 := by
  have h := congrArg τ X.ξ0_im
  rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg] at h
  have := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at this
  linarith

theorem norm_dmin_ortho {y : Frame X.Ψ r} (ho : X.IsOrtho y) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm y τ i‖ = 1 := by
  unfold dmin lminor
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp, sgn]
  split_ifs <;> simp

theorem hermForm_diag {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) (s : X.Ψ → ℝ) (p q : X.Ψ × Fin r → ℂ) :
    hermForm (Matrix.diagonal fun j => ((s (idx j).1 : ℝ) : ℂ)) (fun j => p (idx j)) (fun j => q (idx j)) =
      ∑ τ, (s τ : ℂ) * ∑ a, p (τ, a) * conj (q (τ, a)) := by
  have : hermForm (Matrix.diagonal fun j => ((s (idx j).1 : ℝ) : ℂ)) (fun j => p (idx j)) (fun j => q (idx j)) =
      ∑ t : X.Ψ × Fin r, (s t.1 : ℂ) * (p t * conj (q t)) := by
    rw [hermForm, dotProduct]
    refine Fintype.sum_equiv idx _ _ fun k => ?_
    rw [Matrix.mulVec_diagonal, Pi.star_apply]
    simp only [RCLike.star_def]
    ring
  rw [this, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]

theorem im_diag {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) {y : Frame X.Ψ r} (ho : X.IsOrtho y) (v w : Fin r → E) :
    (hermForm (Matrix.diagonal fun j => ((-2 * ((idx j).1.1 X.ξ0).im : ℝ) : ℂ)) (fun j => pc X y v (idx j))
      (fun j => pc X y w (idx j))).im = ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v w) : ℚ) : ℝ) := by
  rw [hermForm_diag X idx (fun τ => -2 * (τ.1 X.ξ0).im), UnitFrame.trace_eq_sum_re X.Ψ X.cmType, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [pc]
  rw [Complex.im_ofReal_mul, UnitFrame.im_sum_periods X.p0 τ.1 X.Gm (mat y τ) (ho τ)]
  have h3 : τ.1 (herm X.Gm v w) = hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 w) := by
    simp [FD.hermC, FD.herm, FD.Data.emb, FD.cc, IsCMField.complexEmbedding_complexConj]
  rw [map_mul, map_neg, h3, Complex.mul_re, Complex.neg_re, Complex.neg_im, re_xi]
  ring

theorem maj_eq {y : Frame X.Ψ r} (hdet : ∀ τ, (mat y τ).det ≠ 0) (ho : X.IsOrtho y) (v : Fin r → E) (τ : X.Ψ) :
    (∑ a, pc X y v (τ, a) * conj (pc X y v (τ, a))).re = X.maj y τ (Data.emb τ.1 v) := by
  set u := (mat y τ)⁻¹ *ᵥ Data.emb τ.1 v with hu
  have h1 : Data.emb τ.1 v = mat y τ *ᵥ u := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet τ)), Matrix.one_mulVec]
  conv_rhs => rw [h1]
  rw [UnipMove.GraphH.maj_ortho X ho, OrthonormalChartBounds.nsq, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  congr 1
  simp only [pc]
  split_ifs with ha
  · have hcol : col (mat y τ) a = mat y τ *ᵥ Pi.single a 1 := by
      ext k; simp [FD.col]
    rw [hcol, h1, UnitFrame.hermC_mulVec, ho τ]
    simp [Matrix.mulVec_diagonal, FD.sgn, ha]
  · rfl

theorem core {x : Frame X.Ψ r} (hx : x ∈ X.dom) {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) {L : Type}
    (φ : L → Fin r → E) (P : L → Fin g → ℂ) (hP : ∀ a j, P a j = pc X x (φ a) (idx j))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (him : ∀ a b, (hermForm Hm (P a) (P b)).im = ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a) (φ b)) : ℚ) : ℝ)) :
    (∀ a, (hermForm Hm (P a) (P a)).re = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 (φ a))) ∧
    (0 < r → X.κ0 = 2 * X.ξ0) ∧
    ∀ j, X.c (idx j).1 * (if ((idx j).2 : ℕ) < X.p0 then
      ‖dmin X.Gm x (idx j).1 (idx j).2.succ / dmin X.Gm x (idx j).1 (idx j).2.castSucc‖⁻¹
      else ‖dmin X.Gm x (idx j).1 (idx j).2.succ / dmin X.Gm x (idx j).1 (idx j).2.castSucc‖) ≤ (Hm j j).re := by
  classical
  have hb := FrameDegreeData.bOf_mem X hx
  have ho := FrameDegreeData.ortho_bOf X hx
  set b := FrameDegreeData.bOf X x
  have hy : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X hx hb
  set N := PerBor.moveMat X.p0 idx b with hN
  have hmove : ∀ a, (fun j => pc X (rmul x b) (φ a) (idx j)) = N *ᵥ P a := fun a =>
    PerBor.moveMat_mulVec X.p0 idx hb X.Gm x (φ a) _ _ (hP a) (fun _ => rfl)
  let s : X.Ψ → ℝ := fun τ => -2 * (τ.1 X.ξ0).im
  have key : Hm = Nᵀ * ((Matrix.diagonal fun j => ((s (idx j).1 : ℝ) : ℂ)) * N.map (starRingEnd ℂ)) := by
    refine UnitDet.eq_of_im_hermForm_eq _ hspan _ _ ?_
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [him, ← UnitDet.hermForm_mulVec, ← hmove, ← hmove]
    exact (im_diag X idx ho _ _).symm
  have hdiag : ∀ j, (Hm j j).re = ∑ k, s (idx k).1 * ‖N k j‖ ^ 2 := by
    intro j
    rw [key, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.map_apply, mul_left_comm, Complex.mul_conj,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hκ : 0 < r → X.κ0 = 2 * X.ξ0 := by
    intro hr
    refine X.κ0_xi.resolve_right fun h => ?_
    have hs : ∀ τ, s τ < 0 := fun τ => by
      have := X.κ0_sign τ
      rw [h, map_neg, map_mul, map_ofNat] at this
      simp at this
      simp only [s]
      linarith
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ⟩ : Nonempty X.Ψ := by
      by_cases h0 : τ0 ∈ X.Ψ
      · exact ⟨⟨_, h0⟩⟩
      · by_contra hn
        exact h0 ((X.cmType τ0).2 fun h' => hn ⟨⟨_, h'⟩⟩)
    let j := idx.symm (τ, ⟨0, hr⟩)
    have h1 := hpos (Pi.single j 1) (by simp)
    have h2 : hermForm Hm (Pi.single j 1) (Pi.single j 1) = Hm j j := by simp [hermForm]
    rw [h2, hdiag] at h1
    exact absurd h1 (not_lt.2 (Finset.sum_nonpos fun k _ =>
      mul_nonpos_of_nonpos_of_nonneg (hs _).le (sq_nonneg _)))
  have hsc : 0 < r → ∀ τ, s τ = X.c τ := by
    intro hr τ
    have := X.κ0_sign τ
    rw [hκ hr, map_mul, map_ofNat] at this
    simp at this
    simp only [s, Data.c]
    rw [← Complex.abs_im_eq_norm.mpr (re_xi X τ.1), abs_of_neg (by linarith)]
    ring
  refine ⟨fun a => ?_, hκ, fun j => ?_⟩
  · rw [key, ← UnitDet.hermForm_mulVec, ← hmove, hermForm_diag X idx s, Complex.re_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Complex.re_ofReal_mul, maj_eq X (fun τ => (hy τ).1) ho, MajInv.maj_rmul X hx hb]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : X.maj x τ (Data.emb τ.1 (φ a)) = 0 := by
        rw [← MajInv.maj_rmul X hx hb, ← maj_eq X (fun τ => (hy τ).1) ho]
        simp
      rw [this, mul_zero, mul_zero]
    · rw [hsc hr]
  · have hr : 0 < r := (idx j).2.pos
    have hc : ∀ τ, 0 ≤ X.c τ := fun τ => by unfold Data.c; positivity
    rw [hdiag]
    simp only [hsc hr]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun k => X.c (idx k).1 * ‖N k j‖ ^ 2)
      (fun k _ => mul_nonneg (hc _) (sq_nonneg _)) (Finset.mem_univ j))
    congr 1
    have h1 := FrameDegreeData.ratio_rmul X x hx hb (idx j).1 (idx j).2
    rw [norm_div, norm_dmin_ortho X ho, norm_dmin_ortho X ho, div_one] at h1
    rw [hN, PerBor.moveMat_diag _ _ hb]
    split_ifs
    · exact (eq_inv_of_mul_eq_one_left h1.symm).symm
    · rw [norm_inv, inv_pow]
      exact eq_inv_of_mul_eq_one_right h1.symm

end Core

theorem riemann_eq_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), GoodEmb c σ → IsUnf U → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → (∀ v, (hermForm Hm (Uw.Pm k x v) (Uw.Pm k x v)).re = ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k v : Fin r → E))) ∧ (0 < r → (U.X k).κ0 = 2 * (U.X k).ξ0) ∧ ∀ (xi : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → (lieFac Dw xi a' * (U.X k).nfac (laU U a' 0 k) x.1)⁻¹ ≤ ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U Uw k x Hm hG hU hR
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hG
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper : ∀ v s, perFr (U.X k) x.1 v (relab c σ s.1) s.2 = pc (U.X k) x.1 v (f s) := by
    intro v s
    have h := hf s
    generalize f s = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    unfold pc
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by simp)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by dsimp only; omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ s.1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  obtain ⟨h1, h2, h3⟩ := core (U.X k) x.2 (Uw.e.trans f) (fun a => (Uw.φ k a : Fin r → E)) (Uw.Pm k x)
    (fun a j => by rw [Uw.Pm_eq, hper]; rfl) (Uw.period k x).2.2.2.1 Hm hR.2.1
    (fun a b => by rw [hR.2.2, ← Uw.iso]; simp)
  refine ⟨h1, h2, fun xi a' hxi => ?_⟩
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hxi0 : 0 < xi := by
    rw [← hxi τ0]
    exact norm_pos_iff.2 ((map_ne_zero τ0).2 (U.X k).ξ0_ne)
  have hpi : 0 < 2 * Real.pi * xi := by positivity
  have e1 : (lieFac Dw xi a')⁻¹ =
      ∏ s : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (2 * Real.pi * xi) ^ ((a' (s.1, (s.2 : ℕ)) : ℝ) / 2) := by
    rw [← Real.rpow_sum_of_pos hpi, Real.rpow_def_of_pos hpi, lieFac, ← Real.exp_neg, ← Finset.sum_div,
      Fintype.sum_sigma]
    congr 1
    ring
  rw [mul_inv, e1, Data.nfac, ← Fintype.prod_prod_type', ← f.prod_comp, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Fintype.prod_sigma']
  refine Finset.prod_le_prod (fun s _ => by positivity) fun s _ => ?_
  have h4 := h3 (Uw.e.symm s)
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at h4
  have hinv := Function.leftInverse_invFun hbij.1 s.1
  have hc : (U.X k).c (f s).1 = 2 * xi := by rw [Data.c, hxi]
  rw [hc] at h4
  set ρ := ‖dmin (U.X k).Gm x.1 (f s).1 (f s).2.succ / dmin (U.X k).Gm x.1 (f s).1 (f s).2.castSucc‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have e2 : (ρ ^ (-(laU U a' 0 k (f s).1 (f s).2 : ℝ) / 2))⁻¹ =
      (if ((f s).2 : ℕ) < (U.X k).p0 then ρ⁻¹ else ρ) ^ ((a' (s.1, (s.2 : ℕ)) : ℝ) / 2) := by
    unfold laU
    rcases hf s with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_pos (by omega), if_neg (by omega), b, hinv, show ((f s).2 : ℕ) - (U.X k).p0 = s.2 by omega,
        neg_div, Real.rpow_neg hρ0, inv_inv]
      simp
    · have t : conjEmb (f s).1.1 = relab c σ s.1 := by
        rw [b]; exact ComplexEmbedding.involutive_conjugate E _
      rw [if_neg (by omega), if_pos (by omega), t, hinv,
        show (U.X k).p0 - 1 - ((f s).2 : ℕ) = s.2 by omega, Real.inv_rpow hρ0]
      simp
  have hρ1 : 0 ≤ (if ((f s).2 : ℕ) < (U.X k).p0 then ρ⁻¹ else ρ) := by split_ifs <;> positivity
  rw [e2, ← Real.mul_rpow hpi.le hρ1]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  have := mul_le_mul_of_nonneg_left h4 Real.pi_pos.le
  calc _ = _ := by ring
    _ ≤ _ := this

end GlobalTheory.RiemMaj
