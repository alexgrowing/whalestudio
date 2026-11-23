import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_kltAt_of_isNkltCentre (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ) (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) (Γ : X → ℚ) (z x : X) (h : IsNkltCentre p n Γ z)
    (hz : z ⤳ x) : ¬ KltAt p n Γ x := by
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  rintro ⟨η', m', g', h₁, h₂, h₃, h₄⟩
  obtain ⟨E, η, m, g, hη, hm, hg, hE, hd⟩ := h
  have h₅ : IsLogEqn p Γ η' z m' g' := fun w hw => h₃ w (hw.trans hz)
  have h₆ := h₄ E (hE.1.of_specializes hz)
  rw [discrep_eq hn h₁ hη h₂ hm h₅ hg hE.1] at h₆
  exact h₆.not_ge hd

end GlobalTheory.PairStep
