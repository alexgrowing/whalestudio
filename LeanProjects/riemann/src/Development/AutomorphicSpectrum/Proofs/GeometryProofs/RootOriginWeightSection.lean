import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginPointCompare
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightComparison
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VsReg

theorem le_exp_mul_pow_of_log_le {P r A B : ℝ} {M : ℕ} (hP : 0 < P) (hr : 1 ≤ r) (hB : B ≤ M)
    (h : Real.log P ≤ A + B * Real.log r) : P ≤ Real.exp A * r ^ M := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr
  have h1 : Real.log P ≤ A + (M : ℝ) * Real.log r := by nlinarith
  calc P = Real.exp (Real.log P) := (Real.exp_log hP).symm
    _ ≤ Real.exp (A + (M : ℝ) * Real.log r) := Real.exp_le_exp.2 h1
    _ = Real.exp A * r ^ M := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hr0]

theorem sing_prod_le_rW_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (n : RootIx Dw → ℤ), ∀ w₀ ∈ mcPts (mCoordIdeal RM.y), ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ᶠ w in 𝓝 w₀, w ∈ mcPts (mCoordIdeal RM.y) → ∀ x : Or.Re.R.X, SameOrbit (Or.Re.R.lift x x) w → Or.Re.π x ∈ Sys.open' → ∏ r, (Or.sing r).h w ^ n r ≤ C * ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) ^ M := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or n w₀ hw₀
  let f : CMType H → Fin (Dw.p + Dw.q) → ℝ := fun τ i => -(n (τ, i) : ℝ)
  let cf : RootIx Dw → ℝ := fun r => GlobalTheory.CompanionTheory.Ar.Small.Fund.fundCo (f r.1) r.2
  let Bf : RootIx Dw → ℝ := fun r => |Real.log ((Or.Re.ref (some r)).h w₀)| + 1
  let T : Set ((Σ k, RM.ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  have hb : ∀ r : RootIx Dw, ∀ᶠ w in 𝓝[T] w₀, |Real.log ((Or.Re.ref (some r)).h w)| ≤ Bf r := by
    intro r
    have hc : ContinuousWithinAt (Or.Re.ref (some r)).h T w₀ :=
      (Or.Re.ref_smooth (some r)).continuousOn w₀ hw₀.1
    have hc' : ContinuousWithinAt (fun w => |Real.log ((Or.Re.ref (some r)).h w)|) T w₀ :=
      (hc.log ((Or.Re.ref (some r)).pos w₀ hw₀.1).ne').abs
    exact (hc'.tendsto.eventually (Iio_mem_nhds (lt_add_one _))).mono fun _ h => le_of_lt h
  have hall : ∀ᶠ w in 𝓝 w₀, w ∈ T → ∀ r : RootIx Dw, |Real.log ((Or.Re.ref (some r)).h w)| ≤ Bf r :=
    eventually_nhdsWithin_iff.1 (Filter.eventually_all.2 hb)
  let A : ℝ := ∑ r, |cf r| * Bf r
  let Bc : ℝ := ∑ r, |cf r| * |Sys.C₅|
  refine ⟨Real.exp A, ⌈Bc⌉₊, (Real.exp_pos _).le, ?_⟩
  filter_upwards [hall] with w hw hwm x hso hop
  have hwT : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := hwm.1
  have hbd := hw hwT

  have hsum : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h w) + Sys.ph (some (τ, i)) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((Or.sing (τ, k)).h w) := by
    intro τ i
    have e := Or.fund_sing τ i x hop
    have hdeg : (Or.Re.ref (some (τ, i))).a = -∑ k ∈ Finset.Iic i, (Or.sing (τ, k)).a := by
      rw [Or.fund_deg τ i]
      simp only [Or.sing_deg]
    have b := OrArch.log_add_sum_of_sameOrbit (Finset.Iic i) (fun k => Or.sing (τ, k)) hdeg hso hwT
    linarith
  have e2 := GlobalTheory.CompanionTheory.Ar.Small.Fund.sum_neg_mul_eq_sum_fundCo f
    (fun r => Real.log ((Or.sing r).h w))
    (fun r => Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x)) hsum
  have hlog : Real.log (∏ r, (Or.sing r).h w ^ n r) =
      ∑ r : RootIx Dw, -f r.1 r.2 * Real.log ((Or.sing r).h w) := by
    rw [Real.log_prod fun r _ => zpow_ne_zero _ ((Or.sing r).pos _ hwT).ne']
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.log_zpow]
    simp [f]

  set L : ℝ := Real.log (ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x)) with hL
  have hre : Real.exp 1 ≤ ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) := by
    have := Sys.norm_le (Or.Re.π x)
    unfold ReciprocityTheory.AnForm.P.rW
    linarith
  have hr1 : 1 ≤ ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) :=
    le_trans (Real.one_le_exp zero_le_one) hre
  have hL1 : 1 ≤ L := (Real.le_log_iff_exp_le (lt_of_lt_of_le one_pos hr1)).2 hre
  have hph : ∀ r : RootIx Dw, |Sys.ph (some r) (Or.Re.π x)| ≤ |Sys.C₅| * L := by
    intro r
    obtain ⟨h1, h2⟩ := (Sys.sing (some r)).2.2.2 (Or.Re.π x) hop
    have hC : Sys.C₅ ≤ |Sys.C₅| := le_abs_self _
    have hC0 : 0 ≤ |Sys.C₅| := abs_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
  have hle : Real.log (∏ r, (Or.sing r).h w ^ n r) ≤ A + Bc * L := by
    rw [hlog, e2]
    have : A + Bc * L = ∑ r, |cf r| * (Bf r + |Sys.C₅| * L) := by
      simp only [A, Bc, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [this]
    refine Finset.sum_le_sum fun r _ => ?_
    have h3 : |Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x)| ≤
        Bf r + |Sys.C₅| * L := (abs_add_le _ _).trans (add_le_add (hbd r) (hph r))
    calc cf r * (Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x))
        ≤ |cf r * (Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x))| := le_abs_self _
      _ = |cf r| * |Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x)| := abs_mul _ _
      _ ≤ |cf r| * (Bf r + |Sys.C₅| * L) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  exact le_exp_mul_pow_of_log_le (Finset.prod_pos fun r _ => zpow_pos ((Or.sing r).pos _ hwT) _)
    hr1 (Nat.le_ceil _) hle

end GlobalTheory.CompanionTheory.Ar.VsReg
