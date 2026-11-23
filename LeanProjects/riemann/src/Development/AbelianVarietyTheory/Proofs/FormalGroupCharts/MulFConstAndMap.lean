import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt

noncomputable section
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.FormalMul

theorem constantCoeff_mulF {T : Type} [CommRing T] {d : ℕ} (F : Fin d → PS T 2 d)
    (hF : ∀ i, constantCoeff (F i) = 0) (N : ℕ) : ∀ j, constantCoeff (mulF F N j) = 0 := by
  induction N with
  | zero => intro j; simp [mulF]
  | succ n ih => exact gp_addOf F hF _ _ ih (gp_pt 0)

theorem mulF_map {T O : Type} [CommRing T] [CommRing O] (io : T →+* O) {d : ℕ} (F : Fin d → PS T 2 d)
    (hF : ∀ i, constantCoeff (F i) = 0) (N : ℕ) :
    ∀ j, mulF (fun i => MvPowerSeries.map io (F i)) N j = MvPowerSeries.map io (mulF F N j) := by
  induction N with
  | zero => intro j; simp [mulF]
  | succ n ih =>
    intro j
    have hs := gt_hasSubst ![mulF F n, pt T (n := 1) d 0]
      (pair_points_zero_constant (constantCoeff_mulF F hF n) (gp_pt 0))
    simp only [mulF, addOf, ev]
    rw [MvPowerSeries.map_subst hs]
    congr 1
    funext p
    rcases p with ⟨a, b⟩
    fin_cases a
    · exact ih b
    · simp [pt]

theorem mulF_const_and_map : ∀ (T O : Type) [CommRing T] [CommRing O] (io : T →+* O) (d : ℕ) (F : FGLaw T d)
    (N : ℕ) (j : Fin d), MvPowerSeries.constantCoeff (mulF F.F N j) = 0 ∧
      mulF (F.mapF io) N j = MvPowerSeries.map io (mulF F.F N j) :=
  fun _ _ _ _ io _ F N j => ⟨constantCoeff_mulF F.F F.const N j, mulF_map io F.F F.const N j⟩

end GlobalTheory.FormalMul
