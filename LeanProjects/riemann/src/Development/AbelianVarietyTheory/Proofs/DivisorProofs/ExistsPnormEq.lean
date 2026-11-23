import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.La1sqEqOfUnXEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeDesc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.OrthoMetric GlobalTheory.SupFull GlobalTheory.CuspUnif GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_pnorm_eq {U U' : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) (hU' : IsUnf U')
    (hpq : 1 ≤ Dw.p + Dw.q) {xr : ℝ} (hξ : ∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = xr)
    (hξ' : ∀ k (τ : E →+* ℂ), ‖τ (U'.X k).ξ0‖ = xr) {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e)
    (la : ∀ k, FD.Wt (U.X k).Ψ r) (k' : U'.Comp) {la' : FD.Wt (U'.X k').Ψ r}
    (hs' : (U'.X k').IsSec la' (rdU U' f k')) : ∀ x₁ ∈ (U'.X k').dom, ∃ (k : U.Comp) (x : (U.X k).dom),
      (U.X k).firstMinimumSq x.1 = (U'.X k').firstMinimumSq x₁ ∧
      (U'.X k').pnorm la' (rdU U' f k') x₁ = (U.X k).pnorm (la k) (rdU U f k) x.1 := by
  intro x₁ hx₁
  have hpos : ∀ (X : FD.Data E r) (b : E →+* ℂ), 0 < 2 * Real.pi * ‖relab c σ b X.ξ0‖ := fun X b =>
    mul_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero _).2 X.ξ0_ne))
  obtain ⟨b, hbB, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U'.X k')).1 x₁ hx₁
  have hx' := FD.OrthogonalFrameDomain.rmul_mem_dom (U'.X k') hx₁ hbB
  rw [← (FD.orthonormalFlagTranslate_holds r (U'.X k')).2.1 _ _ hs'.2.1 x₁ hx₁ b hbB,
    PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ ho), ← AR.Inst.firstMinimumSq_rightBorel _ hx₁ hbB]
  have hN := isMetric_of_isOrtho E H Dw l Xo c σ r U' hσ hU' hpq k' ⟨_, hx'⟩ ho
  have hrd' : ‖rdU U' f k' (FD.rmul x₁ b)‖ = cabs (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := by
    have e : rdU U' f k' (FD.rmul x₁ b) = toC (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := dif_pos hx'
    rw [e]; rfl
  rw [hrd']
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.T.exists_orthonormalFrame_borelChange_complexFramedPoint E H Dw l Xo c σ r U hU (U'.un k' ⟨_, hx'⟩)
  refine ⟨k, x, la1sq_eq_of_un_x_eq hσ hU hU' hpq hx (x' := ⟨_, hx'⟩) ho ht.1, ?_⟩
  generalize U'.un k' ⟨_, hx'⟩ = y at hN ht ⊢
  obtain ⟨g, hg0, hgd, hchg⟩ :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hm0 := isMetric_of_isOrtho E H Dw l Xo c σ r U hσ hU hpq k x hx
  have hm1 := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨hNN, hG⟩ := GlobalTheory.T.metric_data_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hnone : cabs (t none : CAt σ) = 1 := by
    rw [_root_.mul_one] at hNN
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hNN.symm
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), cabs (t (some p) : CAt σ) = 1 := by
    rintro ⟨τ, i⟩
    rw [← hgd τ i]
    refine (OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ))
      (2 * Real.pi * ‖relab c σ τ (U.X k).ξ0‖ / (2 * Real.pi * ‖relab c σ τ (U'.X k').ξ0‖))
      (div_pos (hpos _ _) (hpos _ _)) (fun i j hij => hg0 τ j i hij) ?_ i).trans ?_
    · have h1 := (congrFun hG τ).symm
      have h2 : ((2 * Real.pi * ‖relab c σ τ (U'.X k').ξ0‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos _ _).ne'
      dsimp only at h1
      rw [Complex.ofReal_div, div_eq_inv_mul, mul_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul,
        inv_mul_cancel₀ h2, one_smul]
    · have h3 := (hpos (U'.X k') τ).ne'
      rw [hξ' k'] at h3
      rw [hξ k, hξ' k', div_self h3]; simp
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hev := GlobalTheory.FlagTan.evR_frBor hf ht
  have hw : cabs ((∏ i, t i ^ e i : (CAt σ)ˣ) : CAt σ) = 1 := by
    let φ : (CAt σ)ˣ →* ℝ := (normHom (α := ℂ)).toMonoidHom.comp (Units.coeHom ℂ)
    have h1 : ∀ i, φ (t i) = 1 := by
      rintro (_ | p)
      exacts [hnone, hsome p]
    let ψ : (CAt σ)ˣ →* ℝˣ := φ.toHomUnits
    have h2 : ∀ i, ψ (t i) = 1 := fun i => Units.ext (h1 i)
    have h3 : ψ (∏ i, t i ^ e i) = 1 := by simp [map_prod, map_zpow, h2]
    exact congrArg Units.val h3
  have hrd : ‖rdU U f k x.1‖ = cabs (evR Xo c f (U.un k x)) := by
    have e : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
    rw [e]; rfl
  rw [PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ hx), hrd, hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw,
    _root_.one_mul]

theorem rdU_mem_holSub {U U' : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) (hU' : IsUnf U')
    (hpq : 1 ≤ Dw.p + Dw.q) {xr : ℝ} (hξ : ∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = xr)
    (hξ' : ∀ k (τ : E →+* ℂ), ‖τ (U'.X k).ξ0‖ = xr) {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e)
    {la : ∀ k, FD.Wt (U.X k).Ψ r} {la' : ∀ k, FD.Wt (U'.X k).Ψ r}
    (hs' : ∀ k', (U'.X k').IsSec (la' k') (rdU U' f k'))
    (h : rdU U f ∈ holSub U.X la) : rdU U' f ∈ holSub U'.X la' := by
  have hr : 0 < r := by have := hU.1; omega
  have hS := Formalism.L2.Pj.abelian₂.holSub_SS FD.siegelSpaceAlgebra_holds _ _ h
  choose B hB using fun k => (hS k).1.2
  choose c₀ hc₀ hgt using fun k => FD.spectralGap_holds r _ _ _ (hS k)
  choose C hC using fun k => FD.cuspidalDecay_holds r _ _ _ _ (hc₀ k).le (hgt k)
  obtain ⟨c₁, hc₁, hle⟩ : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ k, c₁ ≤ c₀ k := by
    cases isEmpty_or_nonempty U.Comp with
    | inl _ => exact ⟨1, one_pos, fun k => isEmptyElim k⟩
    | inr _ =>
      obtain ⟨k, hk⟩ := Finite.exists_min c₀
      exact ⟨c₀ k, hc₀ k, hk⟩
  refine holCusp_mem_holSub _ _ fun k' => ?_
  have hE := exists_pnorm_eq hσ hU hU' hpq hξ hξ' hf la k' (hs' k')
  refine mem_SS_of_decay _ hr _ _ ⟨hs' k', ∑ k, |B k|, fun x₁ hx₁ => ?_⟩ (C := ∑ k, |C k|) (c := 2 * Real.pi * c₁)
    (by positivity) fun x₁ hx₁ => ?_
  · obtain ⟨k, x, -, h2⟩ := hE x₁ hx₁
    rw [h2]
    exact ((hB k x.1 x.2).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun k => |B k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k))
  obtain ⟨k, x, h1, h2⟩ := hE x₁ hx₁
  have hl : 0 < (U.X k).firstMinimumSq x.1 := Real.sqrt_pos.1 (AR.Inst.la1_pos_of_mem_dom _ hr x.2)
  have h3 : Real.exp (-2 * Real.pi * c₀ k / (U.X k).firstMinimumSq x.1) ≤ Real.exp (-(2 * Real.pi * c₁) / (U.X k).firstMinimumSq x.1) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by nlinarith [hle k, Real.pi_pos]) hl.le)
  rw [h2, ← h1]
  calc _ ≤ |C k| * Real.exp (-(2 * Real.pi * c₁) / (U.X k).firstMinimumSq x.1) :=
        (hC k x.1 x.2).trans (mul_le_mul (le_abs_self _) h3 (Real.exp_pos _).le (abs_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun k => |C k|)
          (fun k _ => by positivity) (Finset.mem_univ k)) (Real.exp_pos _).le

def Decr (Dw : Datum H) (G : WTZ E) : Prop :=
  Even G.2 ∧ ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)

def UnifOf (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xr : ℝ) : Prop :=
  ∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xr

theorem cuspW_le {U U' : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {xr : ℝ} (hU : UnifOf U xr) (hU' : UnifOf U' xr)
    (hκ : Nonempty (GlobalTheory.ShFam.KeySec Xo c)) (hpq : 1 ≤ Dw.p + Dw.q) {G : WTZ E} (hG : Decr Dw G) :
    cuspW Xo c U G ≤ cuspW Xo c U' G := fun f hf => by
  rw [mem_cuspW] at hf ⊢
  exact ⟨hf.1, fun σ hσ => rdU_mem_holSub hσ (hU σ hσ).1 (hU' σ hσ).1 hpq (hU σ hσ).2 (hU' σ hσ).2 hf.1
    (GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU E H Dw l Xo c σ r (U' σ) hκ hσ (hU' σ hσ).1 hpq G hG.1 hG.2 f hf.1) (hf.2 σ hσ)⟩

theorem homN_le {U U' : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {xr : ℝ} (hU : UnifOf U xr) (hU' : UnifOf U' xr)
    (hκ : Nonempty (GlobalTheory.ShFam.KeySec Xo c)) (hpq : 1 ≤ Dw.p + Dw.q) {G : WTZ E} (hG : Decr Dw G)
    {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c (exZ Dw G)) {Z : Comp Xo c} (hZ : f ∈ suppOn Z) (x : ℝ) {R : ℝ}
    (hR : 0 ≤ R) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (h : ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G f z ≤ R)
    (z : Σ k, FD.Frame ((U' σ).X k).Ψ r) (hz : z.2 ∈ ((U' σ).X z.1).dom) : homN (U' σ) x G f z ≤ R := by
  obtain ⟨k, y, -, h2⟩ := exists_pnorm_eq hσ (hU σ hσ).1 (hU' σ hσ).1 hpq (hU σ hσ).2 (hU' σ hσ).2 hf
    (modelWt (U σ) G) z.1
    (GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU E H Dw l Xo c σ r (U' σ) hκ hσ (hU' σ hσ).1 hpq G hG.1 hG.2 f hf z.1) z.2 hz
  have e : homN (U' σ) x G f z = homN (U σ) x G f ⟨k, y.1⟩ := congrArg (lieFacZ Dw x G * ·) h2
  rw [e]
  by_cases hy : (⟨k, y.1⟩ : Σ k, FD.Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
  · exact h _ hy
  · have h0 := rdU_eq_zero (U σ) hZ hy
    have : homN (U σ) x G f ⟨k, y.1⟩ = 0 := by
      simp only [homN, ptN, FD.Data.pnorm]
      rw [h0]; simp
    exact this ▸ hR

end GlobalTheory.SlopeDesc
