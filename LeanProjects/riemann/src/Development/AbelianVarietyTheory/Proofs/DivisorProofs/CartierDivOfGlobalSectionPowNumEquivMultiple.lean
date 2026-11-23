import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PairStep

theorem eff_divOfSec_of_sec {X : Scheme.{0}} [IsIntegral X] {L : LB X} (hL : L.IsLB) (s : L.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) : (divOfSec hL s hs).Eff := by
  refine CartierDiv.eff_iff.2 fun y g hg => ?_
  obtain ⟨i, hi⟩ := exists_chart hL y
  have h1 := (presents_divOfRatSec hL (isRatSec_ratOfSec s hs)).isEqn i y hi
  have hu := h1.iff_unitAt.1 hg
  have hr : RegAt y (ratOfSec s hs i : X.functionField) := by
    rw [val_ratOfSec (gen_mem hi)]
    exact regAt_fnOf hi (gen_mem hi) _
  have := hu.regAt.mul hr
  rwa [div_mul_cancel₀ _ (Units.ne_zero _)] at this

theorem qNum_divOfSec : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (hN : N.IsLB) (l m : ℕ) (s : (lbPow N l).Sec) (hs : genericPoint X ∈ nonzeroLocus s), 0 < m → (divOfSec (isLB_lbPow hN l) s hs).Eff ∧ QNum p N ((l : ℚ) / m) (qWeil (divOfSec (isLB_lbPow hN l) s hs) m) := by
  intro X _ _ p hp N hN l m s hs hm
  have hE := eff_divOfSec_of_sec (isLB_lbPow hN l) s hs
  refine ⟨hE, m, _, hm, hE, rfl, fun C hC => ?_⟩
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  letI := algebraΓOfHom p
  have hcls : toPic (divOfSec (isLB_lbPow hN l) s hs) = cls _ (isLB_lbPow hN l) :=
    (presents_divOfRatSec (isLB_lbPow hN l) (isRatSec_ratOfSec s hs)).toPic_eq
  rw [interNumRed_one_congr (isLB_toLB _) (isLB_lbPow hN l) hcls, hC.interNumRed_lbPow hH hN l]
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

end GlobalTheory.PairStep
