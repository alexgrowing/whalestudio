import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jeq_pow_congr {R σ : Type} [CommRing R] {m : ℕ} {a b : MvPowerSeries σ R} (h : JEq m a b) (n : ℕ) :
    JEq m (a ^ n) (b ^ n) := by
  classical
  induction n with
  | zero => intro e _; rw [pow_zero, pow_zero]
  | succ n ih =>
    intro e he
    rw [pow_succ, pow_succ, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hd : p.1.degree + p.2.degree = e.degree := by rw [← map_add, hp]
    rw [ih p.1 (by omega), h p.2 (by omega)]

theorem jeq_psubst_congr {R σ : Type} [CommRing R] {m : ℕ} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (h : JEq m a b)
    (F : PowerSeries R) : JEq m (PowerSeries.subst a F) (PowerSeries.subst b F) := by
  intro e he
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hb)]
  refine finsum_congr fun n => ?_
  rw [jeq_pow_congr h n e he]

theorem jeq_expS_iff_and_exists_log : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d m : ℕ), (∀ f g : PS k n d, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff g = 0 → (JEq m f g ↔ JEq m (FB.expS k f) (FB.expS k g))) ∧ ∀ u : PS k n d, MvPowerSeries.constantCoeff u = 1 → ∃ lam : PS k n d, MvPowerSeries.constantCoeff lam = 0 ∧ FB.expS k lam = u := by
  intro k _ _ n d m
  refine ⟨fun f g hf hg => ⟨fun h => jeq_psubst_congr hf hg h _, fun h => ?_⟩, fun u hu => ?_⟩
  · have h1 : JEq m (PowerSeries.subst f (PowerSeries.exp k) - 1) (PowerSeries.subst g (PowerSeries.exp k) - 1) := by
      intro e he
      rw [map_sub, map_sub]
      exact congrArg (· - _) (h e he)
    have h2 := jeq_psubst_congr (by simp [TB.WickVanishing.constantCoeff_exp hf]) (by simp [TB.WickVanishing.constantCoeff_exp hg]) h1
      (PowerSeries.log k)
    rwa [TB.WickVanishing.log_exp hf, TB.WickVanishing.log_exp hg] at h2
  · exact ⟨_, TB.WickVanishing.constantCoeff_logS hu, TB.WickVanishing.exp_log hu⟩

end GlobalTheory.ChartCmp
