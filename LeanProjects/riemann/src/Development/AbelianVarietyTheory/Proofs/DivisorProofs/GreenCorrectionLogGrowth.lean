import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialLogGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeOfCompList

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open AlgebraicGeometry CategoryTheory Matrix GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.GradedCompare GlobalTheory.InterpMetricLog GlobalTheory.ArDegIndep
open scoped ENNReal Classical ComplexOrder

namespace GlobalTheory.OtherInterpLog

theorem cmp_trans {n : ℕ} {m m' : ℝ} {A B C : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) (h' : Cmp m' B C) (hm : 0 ≤ m)
    (hm' : 0 ≤ m') : Cmp (m * m') A C := by
  have h0 : (0 : ℂ) ≤ (m : ℂ) := Complex.zero_le_real.2 hm
  have h0' : (0 : ℂ) ≤ (m' : ℂ) := Complex.zero_le_real.2 hm'
  constructor
  · have e : (((m * m' : ℝ) : ℂ) • C) - A = (m : ℂ) • (((m' : ℂ) • C) - B) + (((m : ℂ) • B) - A) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact (h'.1.smul h0).add h.1
  · have e : (((m * m' : ℝ) : ℂ) • A) - C = (m' : ℂ) • (((m : ℂ) • A) - B) + (((m' : ℂ) • B) - C) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact (h.2.smul h0').add h'.2

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem hodge_gram_eq (x x' : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ)
    (hy : ¬ LiesIn y (genBd s.T.Z)) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    (x'.hodge σ).gram y g τ = (x.hodge σ).gram y g τ := by
  obtain ⟨f, hf⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hy
  rw [x.hodge_gram hf, x'.hodge_gram hf]

theorem cmp_interp_other (x x' : ToroidalCompactificationData s) {C C' : ℝ} (hC : x.IsMuExp C) (hC' : x'.IsMuExp C') (σ : κ.c.F →+* ℂ) (R : ℝ)
    (y : CxPts (genStr s.T.Z) σ) (hy : ¬ LiesIn y (genBd s.T.Z)) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z))
    (τ : D.host.E →+* ℂ) :
    Cmp (x'.r σ y ^ C' * x'.r σ y ^ C' * x.r σ y ^ C) ((x'.eigMetAt σ (some R)).gram y g τ) ((x.eigMet σ).gram y g τ) := by
  have hr : 0 ≤ x.r σ y ^ C := Real.rpow_nonneg ((Real.exp_pos 1).le.trans (x.exp_le_r σ y)) _
  have hr' : 0 ≤ x'.r σ y ^ C' := Real.rpow_nonneg ((Real.exp_pos 1).le.trans (x'.exp_le_r σ y)) _
  have h1 := cmp_trans (cmp_interp x' hC' σ R y hy g τ) (cmp_hodge x' hC' σ y hy g τ) hr' hr'
  rw [hodge_gram_eq x x' σ y hy] at h1
  exact cmp_trans h1 (cmp_hodge x hC σ y hy g τ).symm (mul_nonneg hr' hr') hr

theorem abs_psiOf_le : Hypotheses2 → HypothesesH → OnObj fun D O A T H h => ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ c : O.Y.Comp, ∃ C : ℝ,
    ∀ (u : Wt O.Y) (σ : Fin ((T.M c).n + 1)) (z : (T.M c).X σ), z ∉ (T.M c).Z σ → ∀ R : ℝ, 2 ≤ R →
      |psiOf h x' R u c σ z| ≤ C * ‖u‖ * Real.log ((T.M c).r σ z) := by
  intro _ _ D O hO _ A T H h x' c
  obtain ⟨x, P, hx⟩ := hO
  obtain ⟨C₀, hC₀⟩ := x.exists_isMuExp
  obtain ⟨C₁, hC₁⟩ := x'.exists_isMuExp
  obtain ⟨L, hL1, hLr⟩ := GlobalTheory.BdFnCompare.exists_log_r_le x x'
  refine ⟨∑ w : DV.Rt D.what₂.Tau O.N, (∑ z : Letter O.S.Dw, |(O.ex w z : ℝ)| * (O.S.Dw.mult z.1 : ℝ)) *
    (2 * C₁ * L + C₀), fun u a z hz R hR => ?_⟩
  have hZ := hz
  rw [(h.an c).Z] at hZ
  rw [(h.an c).r a z hz]
  unfold psiOf chgWith
  rw [hx.h0_eq, hx.r_eq]
  have hy : ¬ LiesIn ((O.Φ.C c).down ((h.man c).pt a z)) (genBd O.s.T.Z) := hZ
  have hr := x.exp_le_r _ ((O.Φ.C c).down ((h.man c).pt a z))
  have hr0 : 0 < x.r _ ((O.Φ.C c).down ((h.man c).pt a z)) := (Real.exp_pos 1).trans_le hr
  have hr1 : 1 ≤ x.r _ ((O.Φ.C c).down ((h.man c).pt a z)) := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hr' := x'.exp_le_r _ ((O.Φ.C c).down ((h.man c).pt a z))
  have hr0' : 0 < x'.r _ ((O.Φ.C c).down ((h.man c).pt a z)) := (Real.exp_pos 1).trans_le hr'
  have hr1' : 1 ≤ x'.r _ ((O.Φ.C c).down ((h.man c).pt a z)) := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have p0 := Real.one_le_rpow hr1 hC₀.1
  have p1 := Real.one_le_rpow hr1' hC₁.1
  have hLy := mul_le_mul_of_nonneg_left (hLr _ _ hy) hC₁.1
  have hL : ∀ w : DV.Rt D.what₂.Tau O.N,
      |lnRatio (metsOf x' O.Φ c (some R) _ (O.ex w)) (refMet x O.Φ c _ (O.ex w)) ((h.man c).pt a z)| ≤
        (∑ z : Letter O.S.Dw, |(O.ex w z : ℝ)| * (O.S.Dw.mult z.1 : ℝ)) *
          ((2 * C₁ * L + C₀) * Real.log (x.r _ ((O.Φ.C c).down ((h.man c).pt a z)))) := fun w => by
    have b := abs_lnRatio_met_le (Y := O.Φ.C c) (x'.eigMetAt _ (some R)) (x.eigMet _) (O.ex w) ((h.man c).pt a z)
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le p1 p1) p0)
      fun g τ => cmp_interp_other x x' hC₀ hC₁ _ R _ hy g τ
    refine b.trans (mul_le_mul_of_nonneg_left ?_
      (Finset.sum_nonneg fun z _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_rpow hr0,
      Real.log_rpow hr0']
    linarith
  have hu : ∀ w : DV.Rt D.what₂.Tau O.N, |u w.1 w.2| ≤ ‖u‖ := fun w => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (u w.1) w.2).trans (norm_le_pi_norm u w.1)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ w : DV.Rt D.what₂.Tau O.N, ‖u‖ * ((∑ z : Letter O.S.Dw, |(O.ex w z : ℝ)| * (O.S.Dw.mult z.1 : ℝ)) *
          ((2 * C₁ * L + C₀) * Real.log (x.r _ ((O.Φ.C c).down ((h.man c).pt a z))))) :=
        Finset.sum_le_sum fun w _ => by
          rw [abs_mul]
          exact mul_le_mul (hu w) (hL w) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [rFlag]
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ => by ring

end GlobalTheory.OtherInterpLog
