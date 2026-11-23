import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportProposition
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

namespace Formalism.L2.SG.WConst

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj Formalism.MainNotions.S.LocalSplitGroups

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LinAlg

variable {r : ℕ}

theorem Dl_scale (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Formalism.L2.SG.RealObj.Dl (r := r) (fun a b => c a * Z a b * c b) l = (∏ a : Fin l, c (Fin.castLE hl a)) ^ 2 * Formalism.L2.SG.RealObj.Dl Z l := by
  simp only [Formalism.L2.SG.RealObj.Dl, dif_pos hl]

  have h : Matrix.submatrix (fun a b => c a * Z a b * c b : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.of (fun i j => c (Fin.castLE hl i) *
        Matrix.of (fun i j => c (Fin.castLE hl j) * (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)) i j) i j) := by
    ext i j
    show c (Fin.castLE hl i) * Z (Fin.castLE hl i) (Fin.castLE hl j) * c (Fin.castLE hl j) =
      c (Fin.castLE hl i) * (c (Fin.castLE hl j) * Z (Fin.castLE hl i) (Fin.castLE hl j))
    ring
  rw [h, Matrix.det_mul_column, Matrix.det_mul_row]
  ring

theorem Gv_scale (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : Fin (r + 1) → ℂ)
    (hc : c (Fin.last r) = 1) :
    Formalism.L2.SG.RealObj.Gv T T' (fun a b => c a * Z a b * c b) = ‖∏ a : Fin r, c a.castSucc‖ ^ 4 * Formalism.L2.SG.RealObj.Gv T T' Z := by
  have h1 := Dl_scale Z c (r + 1) (le_refl (r + 1))
  have h0 := Dl_scale Z c r (Nat.le_succ r)
  have hp1 : (∏ a : Fin (r + 1), c (Fin.castLE (le_refl (r + 1)) a)) = ∏ a : Fin r, c a.castSucc := by
    rw [Fin.prod_univ_castSucc]
    show (∏ a : Fin r, c a.castSucc) * c (Fin.last r) = _
    rw [hc, mul_one]
  have hp0 : (∏ a : Fin r, c (Fin.castLE (Nat.le_succ r) a)) = ∏ a : Fin r, c a.castSucc := rfl
  simp only [Formalism.L2.SG.RealObj.Gv]
  rw [h1, h0, hp1, hp0, norm_mul, norm_mul, norm_pow]
  ring

private theorem norm_Dl_ZhatO_eq_norm_Dl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : ℕ) :
    ‖Formalism.L2.SG.RealObj.Dl (Formalism.L2.SG.RealObj.ZhatO Z) l‖ = ‖Formalism.L2.SG.RealObj.Dl Z l‖ := by
  simp only [Formalism.L2.SG.RealObj.Dl]
  split_ifs with hl
  · have h : ((Formalism.L2.SG.RealObj.ZhatO Z).submatrix (Fin.castLE hl) (Fin.castLE hl)) =
        Matrix.of (fun i j => (-1 : ℂ) ^ (r - (Fin.castLE hl j).1) *
          (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)) i j) := by
      ext i j
      rfl
    rw [h, Matrix.det_mul_row, norm_mul]
    simp
  · rfl

theorem Gv_zhatO (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Formalism.L2.SG.RealObj.Gv T T' (Formalism.L2.SG.RealObj.ZhatO Z) = Formalism.L2.SG.RealObj.Gv T T' Z := by
  simp only [Formalism.L2.SG.RealObj.Gv, norm_Dl_ZhatO_eq_norm_Dl]

end LinAlg

section Scale

theorem sum_range_sub_two (r : ℕ) : (∑ i ∈ Finset.range r, (r - i)) * 2 = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [add_mul, ih]
    ring

theorem sum_sub_two (r : ℕ) : (∑ a : Fin r, (r - a.1)) * 2 = r * (r + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - i) r]
  exact sum_range_sub_two r

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ZX_scale (u u' : D.what₂.Word) (sc : ℝ) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    ZX X u u' sc γ v = fun a b => ((sc : ℂ) ^ (D.R.rS - a.1))⁻¹ * ZX X u u' 1 γ v a b * ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹ := by
  funext a b
  simp [ZX, Formalism.L2.SG.RealObj.Zhat, frm, famSc, Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul, star_smul]
  ring

theorem GX_scale (u u' : D.what₂.Word) {sc : ℝ} (hsc : 0 < sc) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    GX X u u' sc γ v = (sc ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * GX X u u' 1 γ v := by
  have hc : ((sc : ℂ) ^ (D.R.rS - (Fin.last D.R.rS).1))⁻¹ = 1 := by simp
  have hG := Gv_scale (Tw u) (Tw u') (ZX X u u' 1 γ v) (fun a => ((sc : ℂ) ^ (D.R.rS - a.1))⁻¹) hc
  beta_reduce at hG
  simp only [GX]
  rw [ZX_scale X u u' sc γ v, hG]
  congr 1
  have hn : ‖∏ a : Fin D.R.rS, ((sc : ℂ) ^ (D.R.rS - (Fin.castSucc a).1))⁻¹‖ =
      (sc ^ (∑ a : Fin D.R.rS, (D.R.rS - a.1)))⁻¹ := by
    rw [norm_prod]
    simp only [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsc, Fin.coe_castSucc]
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
  have hS : (∑ a : Fin D.R.rS, (D.R.rS - a.1)) * 4 = 2 * D.R.rS * (D.R.rS + 1) := by
    have h2 := sum_sub_two D.R.rS
    calc (∑ a : Fin D.R.rS, (D.R.rS - a.1)) * 4 = ((∑ a : Fin D.R.rS, (D.R.rS - a.1)) * 2) * 2 := by ring
      _ = 2 * D.R.rS * (D.R.rS + 1) := by rw [h2]; ring
  rw [hn, inv_pow, ← pow_mul, hS]

end Scale

section Pt

theorem prod_normSq_embS (D : D7) (x : D.host.E) :
    ∏ τ : D.what₂.Tau, ‖Formalism.MainNotions.S.embS D τ x‖ ^ 2 = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [Formalism.MainNotions.InterlacingSignCuts.prod_places D] at h
  rw [← h]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [InfinitePlace.mult_isComplex ⟨_, IsTotallyComplex.isComplex _⟩, Formalism.MainNotions.InterlacingSignCuts.plOf_apply]
  rfl

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ptC_eq (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) :
    ptC X v w = (ptMat w).map (Formalism.MainNotions.S.embS D (X.pl v)) := by
  simp only [ptC, X.φ_eq, RingEquiv.apply_symm_apply]

theorem Dl_ptC (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    Formalism.L2.SG.RealObj.Dl (ptC X v w) l = Formalism.MainNotions.S.embS D (X.pl v) (Dmin w l) := by
  rw [ptC_eq]
  simp only [Formalism.L2.SG.RealObj.Dl, dif_pos hl, Dmin]
  rw [RingHom.map_det]
  rfl

private theorem embS_conjF_eq_conj_embS (τ : D.what₂.Tau) (x : D.host.E) :
    Formalism.MainNotions.S.embS D τ (D.conjF x) = starRingEnd ℂ (Formalism.MainNotions.S.embS D τ x) :=
  Formalism.L2.SG.Pf.emb_conjF τ x

theorem Gv_ptC (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) :
    Gv (Tw u) (Tw u') (ptC X v w) =
      (Formalism.MainNotions.S.embS D (X.pl v) (Gpt (D.mem u).A.T (D.mem u').A.T w)).re := by
  simp only [Gv]
  rw [Dl_ptC X v w (D.R.rS + 1) le_rfl, Dl_ptC X v w D.R.rS (Nat.le_succ _)]
  simp only [Gpt, map_sub, map_mul, map_natCast, embS_conjF_eq_conj_embS, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, Tw]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re]

theorem embS_GPoint_im (τ : D.what₂.Tau) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).im = 0 := by
  simp only [Gpt, map_sub, map_mul, map_natCast, embS_conjF_eq_conj_embS, Complex.mul_conj]
  simp

end Pt

section Prod

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem card_places : Fintype.card (InfinitePlace X.B.I.F) = D.R.f := by
  rw [Fintype.card_congr X.pl, D.what₂.card_Tau]

theorem isPtRep_gamW {u u' : D.what₂.Word} {w : Point D.host.E (D.R.rS + 1)} (h : ∃ γ, IsPtRep X u u' w γ) :
    IsPtRep X u u' w (gamW X u u' w) := by
  simp only [gamW, dif_pos h]
  exact h.choose_spec

theorem GX_gamW (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (h : ∃ γ, IsPtRep X u u' w γ)
    (v : InfinitePlace X.B.I.F) :
    GX X u u' D.host.rdE (gamW X u u' w) v = (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ *
      (Formalism.MainNotions.S.embS D (X.pl v) (Gpt (D.mem u).A.T (D.mem u').A.T w)).re := by
  rw [GX_scale X u u' (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D) (gamW X u u' w) v]
  congr 1
  simp only [GX]
  rw [← Gv_zhatO, isPtRep_gamW X h v, Gv_ptC]

theorem prod_re_embS_GPoint (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (hT : TotPos (Gpt T T' w)) :
    ∏ τ : D.what₂.Tau, (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re =
      Real.sqrt ((|Algebra.norm ℚ (Gpt T T' w)| : ℚ) : ℝ) := by
  have hpos : ∀ τ : D.what₂.Tau, 0 < (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re := fun τ => hT τ
  have hnorm : ∀ τ : D.what₂.Tau, ‖Formalism.MainNotions.S.embS D τ (Gpt T T' w)‖ = (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re := by
    intro τ
    have e : Formalism.MainNotions.S.embS D τ (Gpt T T' w) = ((Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re : ℂ) := by
      apply Complex.ext <;> simp [embS_GPoint_im τ T T' w]
    rw [congrArg norm e, Complex.norm_real, Real.norm_of_nonneg (hpos τ).le]
  calc ∏ τ : D.what₂.Tau, (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re
      = Real.sqrt ((∏ τ : D.what₂.Tau, (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re) ^ 2) :=
        (Real.sqrt_sq (Finset.prod_nonneg fun τ _ => (hpos τ).le)).symm
    _ = Real.sqrt (∏ τ : D.what₂.Tau, ‖Formalism.MainNotions.S.embS D τ (Gpt T T' w)‖ ^ 2) := by
        rw [← Finset.prod_pow]
        simp only [hnorm]
    _ = _ := by rw [prod_normSq_embS]

theorem prod_GX_gamW (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (h : ∃ γ, IsPtRep X u u' w γ)
    (hT : TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w)) :
    ∏ v, GX X u u' D.host.rdE (gamW X u u' w) v =
      ((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹) ^ D.R.f *
        Real.sqrt ((|Algebra.norm ℚ (Gpt (D.mem u).A.T (D.mem u').A.T w)| : ℚ) : ℝ) := by
  simp only [GX_gamW X u u' w h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_places]
  congr 1
  rw [← prod_re_embS_GPoint _ _ w hT]
  exact Fintype.prod_equiv X.pl _ _ (fun v => rfl)

end Prod

end Formalism.L2.SG.WConst
