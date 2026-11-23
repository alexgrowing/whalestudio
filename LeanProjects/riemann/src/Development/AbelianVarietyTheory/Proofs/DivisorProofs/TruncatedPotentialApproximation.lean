import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGradedNormLeOfComparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedFormComparisonPosSemidefStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.GradedNorm
open scoped ComplexOrder

namespace GlobalTheory.InterpClose

theorem psd_smul_sub {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (hN : N.IsHermitian) (a : ℝ)
    (h : ∀ v : Fin n → ℂ, (star v ⬝ᵥ N *ᵥ v).re ≤ a * (star v ⬝ᵥ M *ᵥ v).re) : ((a : ℂ) • M - N).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ((hM.smul (show star (a : ℂ) = a from Complex.conj_ofReal a)).sub hN) fun v => ?_
  have e : star v ⬝ᵥ ((a : ℂ) • M - N) *ᵥ v = (a : ℂ) * (star v ⬝ᵥ M *ᵥ v) - star v ⬝ᵥ N *ᵥ v := by
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [e, Complex.nonneg_iff]
  have h1 : (star v ⬝ᵥ M *ᵥ v).im = 0 := hM.im_star_dotProduct_mulVec_self v
  have h2 : (star v ⬝ᵥ N *ᵥ v).im = 0 := hN.im_star_dotProduct_mulVec_self v
  constructor
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith [h v]
  · simp [Complex.sub_im, Complex.mul_im, h1, h2]

section Flag
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {σ : F →+* ℂ}

theorem pn_met_chosen (G : EigMet Z (embOf e σ)) (n : Letter Dw → ℤ) (f : Y.Y.FnC σ) (p : Y.Y.pts σ) :
    pn Y.Y σ _ (Y.met G n) f p =
      ‖fval (prodPow (Y.exists_adapted p).choose.1 n) f p‖ ^ 2 * Y.genSq G n (Y.exists_adapted p).choose.2 := by
  rw [pn_eq (FlagCpt.prodPow_mem n (Y.exists_adapted p).choose_spec.1), FlagCpt.met_h G n (Y.exists_adapted p).choose_spec.2]
  simp [prodPow]

theorem log_genSq (G : EigMet Z (embOf e σ)) (n : Letter Dw → ℤ) {p : Y.Y.pts σ} (g : Y.FrameAt p) :
    Real.log (Y.genSq G n g) = ∑ w : Letter Dw, (n w : ℝ) * Real.log (grSq (G.gram _ g w.1) w.2) := by
  rw [FlagCpt.genSq, Real.log_prod (fun w _ => (zpow_pos (grSq_pos (G.pos _ _ _) _) _).ne')]
  exact Finset.sum_congr rfl fun w _ => Real.log_zpow _ _

theorem log_pn_sub (G G' : EigMet Z (embOf e σ)) (n : Letter Dw → ℤ) (f : Y.Y.FnC σ) (p : Y.Y.pts σ)
    (h : 0 < pn Y.Y σ _ (Y.met G n) f p) :
    Real.log (pn Y.Y σ _ (Y.met G n) f p) - Real.log (pn Y.Y σ _ (Y.met G' n) f p) =
      ∑ w : Letter Dw, (n w : ℝ) * (Real.log (grSq (G.gram _ (Y.exists_adapted p).choose.2 w.1) w.2) -
        Real.log (grSq (G'.gram _ (Y.exists_adapted p).choose.2 w.1) w.2)) := by
  rw [pn_met_chosen] at h ⊢
  rw [pn_met_chosen]
  have ha : ‖fval (prodPow (Y.exists_adapted p).choose.1 n) f p‖ ^ 2 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h
  rw [Real.log_mul ha (Y.genSq_pos G n _).ne', Real.log_mul ha (Y.genSq_pos G' n _).ne', log_genSq, log_genSq]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end Flag

section Obj

variable {D : D7} {O : Setup D} {x : ToroidalCompactificationData O.s} {P : PolOf x O.Φ}

def bnd (O : Setup D) : ℝ :=
  ∑ y : DV.Rt D.what₂.Tau O.N, ∑ w : Letter O.S.Dw, |(O.ex y w : ℝ)| * (2 * (O.S.Dw.mult w.1 : ℝ))

theorem chg_sub (hW : O.CoreWith x P) (c : O.s.Comp) (R : ℝ) (u : D.what₂.Tau → Fin O.N → ℝ) (σ : D.what₂.LL →+* ℂ)
    (z : Pts (O.var c) σ) :
    O.chg c (some R) u σ z - O.chg c none u σ z = ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 * (∑ w : Letter O.S.Dw,
      (O.ex y w : ℝ) * (Real.log (grSq ((x.eigMetAt (embOf O.κ.e σ) (some R)).gram _
          ((O.Φ.C c).exists_adapted z).choose.2 w.1) w.2) -
        Real.log (grSq ((x.eigMetAt (embOf O.κ.e σ) none).gram _ ((O.Φ.C c).exists_adapted z).choose.2 w.1) w.2))) / 2 := by
  have hC : O.Core := ⟨x, P, hW⟩
  simp only [Setup.chg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hp := hC.posAt_hm c σ (some R) (O.ex y) z
  unfold PosAt at hp
  rw [hW.hm_eq] at hp
  have key := log_pn_sub (O.Φ.C c) (x.eigMetAt (embOf O.κ.e σ) (some R)) (x.eigMetAt (embOf O.κ.e σ) none) (O.ex y) _ z hp
  have e : lnN (O.met.hm c (some R) σ (O.ex y)) (genAt (divOf (O.Φ.C c) (O.ex y)) (under z)) z -
      lnN (O.met.hm c none σ (O.ex y)) (genAt (divOf (O.Φ.C c) (O.ex y)) (under z)) z = (∑ w : Letter O.S.Dw,
      (O.ex y w : ℝ) * (Real.log (grSq ((x.eigMetAt (embOf O.κ.e σ) (some R)).gram _
          ((O.Φ.C c).exists_adapted z).choose.2 w.1) w.2) -
        Real.log (grSq ((x.eigMetAt (embOf O.κ.e σ) none).gram _ ((O.Φ.C c).exists_adapted z).choose.2 w.1) w.2))) / 2 := by
    rw [hW.hm_eq]
    simp only [lnN]
    rw [← sub_div, ← key]
    rfl
  simp only [lnRatio]
  linear_combination u y.1 y.2 * e

theorem log_inv_one_sub_le {R : ℝ} (hR : 2 ≤ R) : Real.log (1 - R⁻¹)⁻¹ ≤ 2 / R := by
  have hR0 : 0 < R := by linarith
  have hm : (1 - R⁻¹)⁻¹ = R / (R - 1) := by field_simp
  have hR1 : 0 < R - 1 := by linarith
  rw [hm]
  refine (Real.log_le_sub_one_of_pos (div_pos hR0 hR1)).trans ?_
  rw [div_sub_one hR1.ne', div_le_div_iff₀ hR1 hR0]
  nlinarith

theorem one_le_inv_one_sub {R : ℝ} (hR : 2 ≤ R) : 1 ≤ (1 - R⁻¹)⁻¹ := by
  have h1 : 0 < 1 - R⁻¹ := by
    have : R⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hR
    linarith
  have h2 : 1 - R⁻¹ ≤ 1 := by have := inv_nonneg.2 (show (0:ℝ) ≤ R by linarith); linarith
  exact one_le_inv₀ h1 |>.2 h2

theorem abs_log_grSq_sub_le (hW : O.CoreWith x P) (c : O.s.Comp) {R : ℝ} (hR : 2 ≤ R) (σ : D.what₂.LL →+* ℂ)
    (z : Pts (O.var c) σ) (hz : (O.Φ.C c).π (under z) ∉ genBd O.s.T.Z) (hr : O.met.r c σ z ≤ Real.sqrt R)
    (w : Letter O.S.Dw) :
    |Real.log (grSq ((x.eigMetAt (embOf O.κ.e σ) (some R)).gram _ ((O.Φ.C c).exists_adapted z).choose.2 w.1) w.2) -
      Real.log (grSq ((x.eigMetAt (embOf O.κ.e σ) none).gram _ ((O.Φ.C c).exists_adapted z).choose.2 w.1) w.2)| ≤
      2 * (O.S.Dw.mult w.1 : ℝ) * (2 / R) := by
  set y := (O.Φ.C c).down z
  set q := ((O.Φ.C c).exists_adapted z).choose.2
  obtain ⟨hC0, hmu⟩ := x.isMuExp_muExp (ToroidalCompactificationData.exists_isMuExp x)
  have hy : ¬ LiesIn y (genBd O.s.T.Z) := hz
  have hr' : x.r (embOf O.κ.e σ) y ≤ Real.sqrt R := by rw [hW.r_eq] at hr; exact hr
  have hr1 : 1 ≤ x.r (embOf O.κ.e σ) y :=
    (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1).trans (x.exp_le_r _ y)
  have hR0 : 0 < R := by linarith
  have hrR2 : x.r (embOf O.κ.e σ) y ≤ R ^ 2 := by
    refine hr'.trans ((Real.sqrt_le_iff).2 ⟨hR0.le, ?_⟩ |>.trans ?_)
    · nlinarith
    · nlinarith
  have hs : x.wt (embOf O.κ.e σ) R y = 1 / (1 + (x.r (embOf O.κ.e σ) y / R) ^ x.kap) := by
    rw [x.wt_eq hR hy, cutWt_of_le _ hR (by linarith) hrR2]
  have hsle : 1 - x.wt (embOf O.κ.e σ) R y ≤ (x.r (embOf O.κ.e σ) y / R) ^ x.kap := by
    have ht : 0 ≤ (x.r (embOf O.κ.e σ) y / R) ^ x.kap := Real.rpow_nonneg (div_nonneg (by linarith) hR0.le) _
    rw [hs]
    have e1 : 1 - 1 / (1 + (x.r (embOf O.κ.e σ) y / R) ^ x.kap) =
        (x.r (embOf O.κ.e σ) y / R) ^ x.kap / (1 + (x.r (embOf O.κ.e σ) y / R) ^ x.kap) := by
      field_simp
      ring
    rw [e1]
    exact div_le_self ht (by linarith)
  have hrC : 0 < x.r (embOf O.κ.e σ) y ^ x.muExp := Real.rpow_pos_of_pos (by linarith) _
  have hB := (x.hodge (embOf O.κ.e σ)).pos y q w.1
  have hB₀ := (x.eigMet (embOf O.κ.e σ)).pos y q w.1
  have h1 : (((x.r (embOf O.κ.e σ) y ^ x.muExp : ℝ) : ℂ) • (x.eigMet (embOf O.κ.e σ)).gram y q w.1 -
      (x.hodge (embOf O.κ.e σ)).gram y q w.1).PosSemidef :=
    psd_smul_sub hB₀.1 hB.1 _ fun v => (hmu _ y hy q w.1 v).2
  have h2 : (((x.r (embOf O.κ.e σ) y ^ x.muExp : ℝ) : ℂ) • (x.hodge (embOf O.κ.e σ)).gram y q w.1 -
      (x.eigMet (embOf O.κ.e σ)).gram y q w.1).PosSemidef := by
    refine psd_smul_sub hB.1 hB₀.1 _ fun v => ?_
    have a := (hmu _ y hy q w.1 v).1
    have e2 : x.r (embOf O.κ.e σ) y ^ x.muExp * x.r (embOf O.κ.e σ) y ^ (-x.muExp) = 1 := by
      rw [Real.rpow_neg (by linarith), mul_inv_cancel₀ hrC.ne']
    have a2 := mul_le_mul_of_nonneg_left a hrC.le
    rw [← mul_assoc, e2, one_mul] at a2
    exact a2
  obtain ⟨k1, k2, k3, k4⟩ := GlobalTheory.T.mixed_form_comparison_posSemidef _ _ _ (x.wt (embOf O.κ.e σ) R y) _ R x.kap x.muExp hB hB₀ hr1 hr' hR hC0
    x.lt_kap (x.wt_mem R y) hsle h1 h2
  have hm1 := one_le_inv_one_sub hR
  have hlog := log_inv_one_sub_le hR
  have hd : (0 : ℝ) ≤ 2 * (O.S.Dw.mult w.1 : ℝ) := by positivity
  have fin : ∀ A : Matrix (Fin (O.S.Dw.mult w.1)) (Fin (O.S.Dw.mult w.1)) ℂ, A.PosDef →
      ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • (x.hodge (embOf O.κ.e σ)).gram y q w.1 - A).PosSemidef →
      ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • A - (x.hodge (embOf O.κ.e σ)).gram y q w.1).PosSemidef →
      |Real.log (grSq A w.2) - Real.log (grSq ((x.hodge (embOf O.κ.e σ)).gram y q w.1) w.2)| ≤
        2 * (O.S.Dw.mult w.1 : ℝ) * (2 / R) := fun A hA a b =>
    (GlobalTheory.T.log_graded_norm_le_of_comparable _ A _ _ hm1 hA hB a b w.2).trans (mul_le_mul_of_nonneg_left hlog hd)
  have hA := (x.eigMetAt (embOf O.κ.e σ) (some R)).pos y q w.1
  simp only [ToroidalCompactificationData.eigMetAt, EigMet.interp] at hA ⊢
  split_ifs at hA ⊢
  · exact fin _ hA k1 k2
  · exact fin _ hA k3 k4

theorem abs_chg_sub_le (hW : O.CoreWith x P) (c : O.s.Comp) {R : ℝ} (hR : 2 ≤ R) (u : D.what₂.Tau → Fin O.N → ℝ)
    (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) (hz : (O.Φ.C c).π (under z) ∉ genBd O.s.T.Z)
    (hr : O.met.r c σ z ≤ Real.sqrt R) :
    |O.chg c (some R) u σ z - O.chg c none u σ z| ≤ bnd O * ‖u‖ / R := by
  have hR0 : 0 < R := by linarith
  rw [chg_sub hW]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [bnd, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_le_sum fun y _ => ?_
  have hu : |u y.1 y.2| ≤ ‖u‖ := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (u y.1) y.2).trans (norm_le_pi_norm u y.1)
  have hS : |∑ w : Letter O.S.Dw, (O.ex y w : ℝ) * (Real.log (grSq ((x.eigMetAt (embOf O.κ.e σ) (some R)).gram _
          ((O.Φ.C c).exists_adapted z).choose.2 w.1) w.2) -
        Real.log (grSq ((x.eigMetAt (embOf O.κ.e σ) none).gram _ ((O.Φ.C c).exists_adapted z).choose.2 w.1) w.2))| ≤
      2 / R * ∑ w : Letter O.S.Dw, |(O.ex y w : ℝ)| * (2 * (O.S.Dw.mult w.1 : ℝ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_left (abs_log_grSq_sub_le hW c hR σ z hz hr w) (abs_nonneg (O.ex y w : ℝ))
    linarith
  have hK : 0 ≤ ∑ w : Letter O.S.Dw, |(O.ex y w : ℝ)| * (2 * (O.S.Dw.mult w.1 : ℝ)) :=
    Finset.sum_nonneg fun w _ => by positivity
  rw [abs_div, abs_mul, abs_two]
  have := mul_le_mul hu hS (abs_nonneg _) (norm_nonneg _)
  have e : ‖u‖ * (2 / R * ∑ w : Letter O.S.Dw, |(O.ex y w : ℝ)| * (2 * (O.S.Dw.mult w.1 : ℝ))) / 2 =
      (∑ w : Letter O.S.Dw, |(O.ex y w : ℝ)| * (2 * (O.S.Dw.mult w.1 : ℝ))) * ‖u‖ / R := by
    field_simp
  rw [← e]
  exact div_le_div_of_nonneg_right this zero_le_two

end Obj

open GlobalTheory.Mean4O in

theorem interp_close_hodge : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c, ∃ C : ℝ, ∀ u σ (R : ℝ), 2 ≤ R → ∀ x, x ∉ (T.M c).Z σ → (T.M c).r σ x ≤ Real.sqrt R → |(T.F c).phR R u σ x - (T.F c).ph u σ x| ≤ C * ‖u‖ / R := by
  intro _ _ D O hC _ A T H h c
  obtain ⟨x, P, hW⟩ := hC
  refine ⟨bnd O, fun u a R hR z hz hr => ?_⟩
  have e1 := (h.an c).phR R hR u a z
  have e2 := (h.an c).ph u a z hz
  erw [e1, e2]
  have hz' := ((h.an c).Z a z).not.1 hz
  rw [(h.an c).r a z hz] at hr
  exact abs_chg_sub_le hW c hR u _ _ hz' hr

end GlobalTheory.InterpClose
