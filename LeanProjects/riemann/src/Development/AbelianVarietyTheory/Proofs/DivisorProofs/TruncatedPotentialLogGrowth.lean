import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLnRatioMetLe

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open AlgebraicGeometry CategoryTheory Matrix GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.GradedCompare
open scoped ENNReal Classical

namespace GlobalTheory.InterpMetricLog

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem cmp_hodge (x : ToroidalCompactificationData s) {C : ℝ} (hC : x.IsMuExp C) (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ)
    (hy : ¬ LiesIn y (genBd s.T.Z)) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    Cmp (x.r σ y ^ C) ((x.eigMet σ).gram y g τ) ((x.hodge σ).gram y g τ) := by
  have hr0 : 0 < x.r σ y := (Real.exp_pos 1).trans_le (x.exp_le_r σ y)
  refine ⟨psd_of_quad (x.gram_posDef g τ) ((x.hodge σ).pos y g τ) fun v => ?_,
    psd_of_quad ((x.hodge σ).pos y g τ) (x.gram_posDef g τ) fun v => (hC.2 σ y hy g τ v).2⟩
  have h1 := (hC.2 σ y hy g τ v).1
  have e : x.r σ y ^ C * x.r σ y ^ (-C) = 1 := by rw [← Real.rpow_add hr0, add_neg_cancel, Real.rpow_zero]
  have hp : 0 ≤ x.r σ y ^ C := (Real.rpow_pos_of_pos hr0 _).le
  calc (star v ⬝ᵥ (x.eigMet σ).gram y g τ *ᵥ v).re
      = x.r σ y ^ C * (x.r σ y ^ (-C) * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re) := by rw [← mul_assoc, e, one_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hp

theorem cmp_interp (x : ToroidalCompactificationData s) {C : ℝ} (hC : x.IsMuExp C) (σ : κ.c.F →+* ℂ) (R : ℝ) (y : CxPts (genStr s.T.Z) σ)
    (hy : ¬ LiesIn y (genBd s.T.Z)) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    Cmp (x.r σ y ^ C) ((x.eigMetAt σ (some R)).gram y g τ) ((x.eigMet σ).gram y g τ) := by
  have hr1 : 1 ≤ x.r σ y := by linarith [x.exp_le_r σ y, Real.add_one_le_exp (1 : ℝ)]
  have hm : 1 ≤ x.r σ y ^ C := Real.one_le_rpow hr1 hC.1
  have h := cmp_hodge x hC σ y hy g τ
  have hA := (x.eigMet σ).pos y g τ
  have hB := (x.hodge σ).pos y g τ
  simp only [ToroidalCompactificationData.eigMetAt, EigMet.interp]
  split_ifs
  · exact (h.mix hA hm (x.wt_mem R y)).symm
  · exact (h.mixDual hA hB hm (x.wt_mem R y)).symm

end GlobalTheory.InterpMetricLog

namespace GlobalTheory.InterpMetricLog

theorem abs_phR_le : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c, ∃ C : ℝ, ∀ u σ x, x ∉ (T.M c).Z σ →
    ∀ R : ℝ, 2 ≤ R → |(T.F c).phR R u σ x| ≤ C * ‖u‖ * Real.log ((T.M c).r σ x) := by
  intro _ _ D O hO _ A T H h c
  obtain ⟨x, P, hx⟩ := hO
  obtain ⟨C₀, hC₀⟩ := x.exists_isMuExp
  refine ⟨∑ w : DV.Rt D.what₂.Tau O.N, (∑ z : Letter O.S.Dw, |(O.ex w z : ℝ)| * (O.S.Dw.mult z.1 : ℝ)) * C₀,
    fun u a z hz R hR => ?_⟩
  have hZ := hz
  rw [(h.an c).Z] at hZ
  have e1 : (T.F c).phR R u a z = O.chg c (some R) u _ ((h.man c).pt a z) := (h.an c).phR R hR u a z
  rw [e1, (h.an c).r a z hz]
  unfold Setup.chg
  rw [hx.hm_eq, hx.h0_eq, hx.r_eq]
  have hy : ¬ LiesIn ((O.Φ.C c).down ((h.man c).pt a z)) (genBd O.s.T.Z) := hZ
  have hr := x.exp_le_r _ ((O.Φ.C c).down ((h.man c).pt a z))
  have hr0 : 0 < x.r _ ((O.Φ.C c).down ((h.man c).pt a z)) := (Real.exp_pos 1).trans_le hr
  have hr1 : 1 ≤ x.r _ ((O.Φ.C c).down ((h.man c).pt a z)) := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL : ∀ w : DV.Rt D.what₂.Tau O.N,
      |lnRatio (metsOf x O.Φ c (some R) _ (O.ex w)) (refMet x O.Φ c _ (O.ex w)) ((h.man c).pt a z)| ≤
        (∑ z : Letter O.S.Dw, |(O.ex w z : ℝ)| * (O.S.Dw.mult z.1 : ℝ)) *
          (C₀ * Real.log (x.r _ ((O.Φ.C c).down ((h.man c).pt a z)))) := fun w => by
    have b := abs_lnRatio_met_le (Y := O.Φ.C c) (x.eigMetAt _ (some R)) (x.eigMet _) (O.ex w) ((h.man c).pt a z)
      (Real.one_le_rpow hr1 hC₀.1) fun g τ => cmp_interp x hC₀ _ R _ hy g τ
    rwa [Real.log_rpow hr0] at b
  have hu : ∀ w : DV.Rt D.what₂.Tau O.N, |u w.1 w.2| ≤ ‖u‖ := fun w => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (u w.1) w.2).trans (norm_le_pi_norm u w.1)
  have hl : 0 ≤ Real.log (x.r _ ((O.Φ.C c).down ((h.man c).pt a z))) := Real.log_nonneg hr1
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ w : DV.Rt D.what₂.Tau O.N, ‖u‖ * ((∑ z : Letter O.S.Dw, |(O.ex w z : ℝ)| * (O.S.Dw.mult z.1 : ℝ)) *
          (C₀ * Real.log (x.r _ ((O.Φ.C c).down ((h.man c).pt a z))))) :=
        Finset.sum_le_sum fun w _ => by
          rw [abs_mul]
          exact mul_le_mul (hu w) (hL w) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [rFlag]
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ => by ring

end GlobalTheory.InterpMetricLog
