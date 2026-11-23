import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FormPolyIsHomogeneousAndEval
import Development.WeilBound.CoreStatements.FlagImmersions.CombLineSmoothConjInvariant
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.re_pot

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

theorem log_line_of_orbit {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (a : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) (x : Re.R.X) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ho : SameOrbit (Re.R.lift x x) z) :
    Real.log ((Re.line a t).h z) = Real.log ((Re.ref a).h z) + S.phT a t (Re.π x) := by
  obtain ⟨c, hc, e⟩ := ho
  have h := Re.line_eq a t h0 h1 x
  rw [e, (Re.line a t).smul c z hc, (Re.ref a).smul c z hc, Re.line_deg] at h
  have hp : (∏ k, ‖c k‖ ^ (Re.ref a).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [Real.log_mul hp ((Re.line a t).pos z hz).ne', Real.log_mul hp ((Re.ref a).pos z hz).ne'] at h
  linarith

theorem samePot_line {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (c : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    SamePot Re.R.A Set.univ (potOf Re.R (Re.line c t)) ((S.potT c t).pullback Re.π Re.holo.1) := by
  intro x _
  obtain ⟨V, hV, hxV, G, hG, hVG⟩ := Re.ref_pot c x (Set.mem_univ x)
  refine ⟨V ∩ Re.R.U x, hV.inter (Re.R.isOpen_U x), ⟨hxV, Re.R.mem_U x⟩, G, ?_, ?_⟩
  · intro j
    exact (hG j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · rintro y ⟨hyV, hyU⟩
    have hm := Re.R.mem x y hyU
    have ho : SameOrbit (Re.R.lift y y) (Re.R.lift x y) := Re.R.compat y x y ⟨Re.R.mem_U y, hyU⟩
    have e1 := log_line_of_orbit Re c t h0 h1 y _ hm.1 ho
    have e2 : Real.log ((Re.ref c).h (Re.R.lift x y)) - (S.th c).φ (Re.π x) (Re.π y) = (G y).re := hVG y hyV
    show Real.log ((Re.line c t).h (Re.R.lift x y)) -
      ((S.th c).φ (Re.π x) (Re.π y) + S.phT c t (Re.π y)) = (G y).re
    linarith

theorem isNull_compl_univ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) :
    IsNull A (Set.univ : Set X)ᶜ := by
  intro j
  simp

theorem mass_eq {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P)
    (Q : Fin D → LocPot Re.R.X) (Φ : Fin D → LocPot S.X) (hΦ : ∀ j, IsPotential S.A (Φ j))
    (hS : ∀ j, SamePot Re.R.A Set.univ (Q j) ((Φ j).pullback Re.π Re.holo.1)) :
    mInt Re.R.A Q (fun _ => 1) = Re.deg * mInt S.A Φ (fun _ => 1) := by
  rw [← degreeFormula S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree Φ hΦ _ continuous_const]
  exact (mInt_congr_samePot D Re.R.X Re.R.A Set.univ Q _ _ _ (isNull_compl_univ _) hS
    (fun j x _ => isC2At_of_isPotential _ (isPotentialPullback S.A Re.R.A Re.π Re.holo _ (hΦ j)) x)
    (fun _ _ => rfl)).1

end PositivityTheory.Xgp.re_pot

theorem PositivityTheory.Xgp.t_re_pot : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), (∀ a t, 0 < t → t ≤ S.t₀ → SamePot Re.R.A Set.univ (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1)) ∧ (∀ (w : Fin D → σ), ptsIntegral P (pot fun j => Re.ref (w j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ (∀ (w : Fin D → σ) (t : Fin D → ℝ), (∀ j, 0 < t j ∧ t j ≤ S.t₀) → ptsIntegral P (pot fun j => Re.line (w j) (t j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ ∀ n : σ → ℤ, IsSmoothHerm (combLine Re.ref n) ∧ geomDeg P (combLine Re.ref n) D = Re.deg * eval (fun a => (n a : ℝ)) S.degPoly := by
  intro hE K _ ι _ D σ _ S P Re
  have href : ∀ w : Fin D → σ,
      mInt Re.R.A (fun j => potOf Re.R (Re.ref (w j))) (fun _ => 1) = Re.deg * S.degNum w := fun w =>
    PositivityTheory.Xgp.re_pot.mass_eq Re _ _ (fun j => (S.sing (w j)).1) fun j => Re.ref_pot (w j)
  refine ⟨fun a t h0 h1 => PositivityTheory.Xgp.re_pot.samePot_line Re a t h0 h1, fun w => ?_, fun w t ht => ?_,
    fun n => ?_⟩
  · rw [ptsIntegral_one_eq_mInt hE resBridge Re.R Re.arith fun j => Re.ref_smooth (w j)]
    exact href w
  · rw [ptsIntegral_one_eq_mInt hE resBridge Re.R Re.arith
        fun j => Re.line_smooth (w j) (t j) (ht j).1 (ht j).2,
      PositivityTheory.Xgp.re_pot.mass_eq Re _ (fun j => S.potT (w j) (t j))
        (fun j => (anSys_open_basics D σ S).2.2.2.1 (w j) (t j) (ht j).1 (ht j).2)
        fun j => PositivityTheory.Xgp.re_pot.samePot_line Re (w j) (t j) (ht j).1 (ht j).2]
    congr 1
    exact massIndep S.A (fun j => S.th (w j)) (fun j => S.phT (w j) (t j)) (fun j => (S.sing (w j)).1)
      fun j => ((S.reg (w j)).2.2 (t j) (ht j).1 (ht j).2).1
  · have hsm : IsSmoothHerm (combLine Re.ref n) := by
      rw [combLine_eq_top]
      exact (RootFieldNumerics.combLine_smooth_conj_invariant K ι σ Re.ref n).1 Re.ref_smooth
    refine ⟨hsm, ?_⟩
    have hQ : ∀ a, IsPotential Re.R.A (potOf Re.R (Re.ref a)) := fun a =>
      isPotential_potOf Re.R (Re.ref_smooth a)
    have h1 : ReciprocityTheory.ChartRestriction.G.Geo.geomDeg P (combLine Re.ref n) D =
        mInt Re.R.A (fun _ : Fin D => potOf Re.R (combLine Re.ref n)) (fun _ => 1) :=
      ptsIntegral_one_eq_mInt hE resBridge Re.R (L := fun _ => combLine Re.ref n) Re.arith fun _ => hsm
    have h2 : mInt Re.R.A (fun _ : Fin D => potOf Re.R (combLine Re.ref n)) (fun _ => 1) =
        mInt Re.R.A (fun _ : Fin D => sumPot (fun a => (n a : ℝ)) fun a => potOf Re.R (Re.ref a))
          (fun _ => 1) := by
      refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr Re.R.A (locDens_congr_of_eqOn Re.R fun _ x y hy => ?_) fun _ => rfl
      have hz := (Re.R.mem x y hy).1
      show Real.log (∏ a, (Re.ref a).h (Re.R.lift x y) ^ n a) =
        ∑ a, (n a : ℝ) * Real.log ((Re.ref a).h (Re.R.lift x y))
      rw [Real.log_prod fun a _ => zpow_ne_zero _ ((Re.ref a).pos _ hz).ne']
      exact Finset.sum_congr rfl fun a _ => Real.log_zpow _ _
    have h3 := (mInt_sumPot_expand D Re.R.X Re.R.A σ Set.univ (fun a => potOf Re.R (Re.ref a))
      (fun _ a => (n a : ℝ)) (fun _ => 1) (PositivityTheory.Xgp.re_pot.isNull_compl_univ _)
      (fun a x _ => PositivityTheory.Xgp.re_pot.isC2At_of_isPotential _ (hQ a) x)
      fun w => mIntegrableCont Re.R.A _ (fun j => hQ (w j)) _ continuous_const).2
    rw [h1, h2, h3, AnSys.degPoly, (formPoly_isHomogeneous_and_eval σ D S.degNum).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [href w]
    ring
